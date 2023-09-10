----------------------------- MODULE CRAQRetry -----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Clients, Nodes, head, tail, NumWrites, NumReads, Objects, MaxTimestamp, initClient, Zookeeper, crasherClient\*, newTail, crashedN 

NumMsgs == 10

RECURSIVE FormChainTopology(_,_)
FormChainTopology(curr, nodes) ==   IF nodes = {}
                                    THEN {<<curr, head>>}
                                    ELSE LET next == CHOOSE node \in nodes : TRUE
                                         IN  {<<curr, next>>} \cup FormChainTopology(next, nodes \ {next})
                                            
NextEdges == FormChainTopology(head, Nodes \ {head})
PrevEdges == { <<e[2], e[1]>> : e \in NextEdges } 


\*EdgesToTail == { <<n, tail>> : n \in Nodes \ {tail}}
\*EdgesFromTail == { <<tail, n>> : n \in Nodes \ {tail}}
\*Edges == NextEdges \cup PrevEdges \cup EdgesToTail \cup EdgesFromTail

Edges == { <<o, p>> \in {<<n, m>>: n \in Nodes, m \in Nodes}: o /= p}   

EdgesFromClients == { <<c, n>> : c \in (Clients \cup {initClient}), n \in Nodes}
EdgesToClients == { <<n, c>> : c \in (Clients \cup {initClient}), n \in Nodes }
ClientEdges == EdgesFromClients \cup EdgesToClients 

EdgesToZookeeper == { <<n, Zookeeper>> : n \in (Nodes \cup Clients) }
EdgesFromZookeeper == { <<Zookeeper, n>> : n \in (Nodes \cup Clients)}
ZookeeperEdges == EdgesToZookeeper \cup EdgesFromZookeeper

EdgesToCrasherClient == { <<n, crasherClient>> : n \in Nodes }
EdgesFromCrasherClient == { <<crasherClient, n>> : n \in Nodes }
CrasherClientEdges == EdgesToCrasherClient \cup EdgesFromCrasherClient 

SelfEdges == { <<n, n>> : n \in Nodes}

Network == Edges \cup ClientEdges \cup ZookeeperEdges \cup CrasherClientEdges \cup SelfEdges

UniqueIdType == {<<c, id>> : c \in Clients, id \in 0..NumMsgs}
NullUniqueId == CHOOSE id : id \notin UniqueIdType
SendersTo(n) == {edge[1]: edge \in {e \in Network: e[2] = n}}

ASSUME  /\ head \in Nodes
        /\ tail \in Nodes
        /\ Cardinality(Nodes) >= 2
\*        /\ Cardinality(Edges) = Cardinality(Nodes \ {head}) * 2 + Cardinality(Nodes \ {tail}) * 2 - 2
\*        /\ Edges \subseteq Network
\*        /\ ClientEdges \subseteq Network
\*        /\ Cardinality(UniqueIdType) = Cardinality(Clients) * (NumMsgs + 1)
        
-----------------------------------------------------------------------------


\* CallType
READ_INV == "READ_INV" \* Read invocation
WRITE_INV == "WRITE_INV" \* Write invocation
READ_RESP == "READ_RESP" \* Read response
WRITE_RESP == "WRITE_RESP" \* Write response

ZK_SESSION_ENDED == "SESSION_ENDED"
NOTCRASHED == "NOTCRASHED"
CRASH == "CRASH"

ZK_NODE_DEL == "ZK_NODE_DEL"
ZK_NODE_ADD == "ZK_NODE_ADD"
ZK_CREATE == "ZK_CREATE"

FAILOVER_PROPAGATE_LOG == "FAILOVER_PROPAGATE_LOG"
FAILOVER_NOTIFY_TAIL == "FAILOVER_NOTIFY_TAIL"
TIMEOUT == "TIMEOUT"


HEAD == "HEAD"
MID == "MID"
TAIL == "TAIL"

\* CommitType
CLEAN == "CLEAN"
DIRTY == "DIRTY"

NullNode == CHOOSE n : n \notin Nodes
NullObj == CHOOSE o \in Objects: TRUE
NullClient == CHOOSE c \in Clients: TRUE

CallType == {READ_INV, WRITE_INV, READ_RESP, WRITE_RESP}
NullCall == CHOOSE call \in CallType: TRUE

CommitType == {CLEAN, DIRTY}
NullCommitStatus == CHOOSE status : status \notin CommitType

TimestampType == { t: t \in 0..MaxTimestamp}
NullTs == CHOOSE ts : ts \notin TimestampType
ObjectVersionType == [  obj: Objects, 
                        uniqueId: UniqueIdType \cup {NullUniqueId}, 
                        writeStartTs: TimestampType \cup {NullTs}, 
                        writeCommitTs: TimestampType \cup {NullTs}, 
                        commitStatus: CommitType \cup {NullCommitStatus}]
NullObjectVersion == {}
             
RequestType == [callType: CallType, 
                uniqueId: UniqueIdType \cup {NullUniqueId},
                startTs: TimestampType \cup {NullTs},
                commitTs: TimestampType \cup {NullTs},
                op: ObjectVersionType]
NullReq == CHOOSE r : r \notin RequestType

Cons(item, seq) == << item >> \o seq   

PendingInvoType == { <<id, node>>: id \in UniqueIdType, node \in Nodes} 
               

(****************************************************************************
--fair algorithm CRAQRetry {

    \* declaration of global algorithms
    variables   msgQs = [edge \in Network |-> << >>], \* in-order delivery via TCP
                failoverMsgQs = [edge \in Network |-> << >>],
                objLogs = [n \in Nodes |-> [o \in Objects |-> << >>]],
                allSubmittedWriteOps = [o \in Objects |-> {}],
                allSubmittedReadOps = [ o \in Objects |-> {}],
                terminatedYet = [c \in Clients |-> FALSE],
                nonInitClients = Clients \ {initClient},
                start = FALSE,
                timeOracle = 10,
                Successors = [n \in Nodes |-> LET e == CHOOSE edge \in NextEdges : edge[1] = n IN e[2]],
                Predecessors = [n \in Nodes |-> LET e == CHOOSE edge \in PrevEdges : edge[1] = n IN e[2]],
                currentHead = head,
                currentTail = tail
                ;
                
    \* operator definitions
    define {
        
        RECURSIVE CommitDirtyVersion(_, _) 
        CommitDirtyVersion(objLog, committedVer) == LET mostRecentVer == Head(objLog)
                                                        uniqueId == committedVer.uniqueId
                                                        writeCommitTs == committedVer.writeCommitTs
                                                    IN  IF mostRecentVer.uniqueId = uniqueId 
                                                        THEN Cons([mostRecentVer EXCEPT !.commitStatus = CLEAN,
                                                                                        !.writeCommitTs = writeCommitTs], 
                                                                   Tail(objLog))
                                                        ELSE Cons(mostRecentVer, CommitDirtyVersion(Tail(objLog), committedVer))
        
        IsDirty(node, obj) == Head(objLogs[node][obj]).commitStatus = DIRTY        
        Read(node, obj) == Head(objLogs[node][obj])
        FindPair(set, k) == CHOOSE kv \in set: kv[1] = k
        Find(set, k) == LET kv == FindPair(set, k) IN kv[2]
        
        Increment(id) == <<id[1], id[2]+1>>
                
        RECURSIVE FindActiveNodes(_)
        FindActiveNodes(node) ==    IF node = currentTail 
                                THEN {node} 
                                ELSE {node} \cup FindActiveNodes(Successors[node])
                                
        ActiveNodes == FindActiveNodes(currentHead)
        
        RECURSIVE FindUnpropagatedWrites(_, _, _)
        FindUnpropagatedWrites(thatObjLogs, thisObjLogs, remainingObjSet) == 
            IF remainingObjSet = {} 
            THEN {}
            ELSE    LET obj == CHOOSE o \in remainingObjSet : TRUE
                    IN  LET thatLog == thatObjLogs[obj]
                            thisLog == thisObjLogs[obj]
                        IN  IF  /\ Head(thatLog).commitStatus = DIRTY 
                                /\ Head(thisLog).commitStatus = CLEAN
                                /\ Head(thatLog).uniqueId /= Head(thisLog).uniqueId
                            THEN {Head(thatLog)} \cup FindUnpropagatedWrites(thatObjLogs, thisObjLogs, remainingObjSet \ {obj})
                            ELSE FindUnpropagatedWrites(thatObjLogs, thisObjLogs, remainingObjSet \ {obj})
                            
        RECURSIVE FindAckdWrites(_, _, _)
        FindAckdWrites(thatObjLogs, thisObjLogs, remainingObjSet) ==
            IF remainingObjSet = {}
            THEN {}
            ELSE    LET obj == CHOOSE o \in remainingObjSet : TRUE
                    IN LET  thatLog == thatObjLogs[obj]
                            thisLog == thisObjLogs[obj]
                       IN   IF  /\ Head(thatLog).uniqueId = Head(thisLog).uniqueId
                                /\ Head(thatLog).commitStatus = DIRTY
                                /\ Head(thisLog).commitStatus = CLEAN
                            THEN {Head(thisLog)} \cup FindAckdWrites(thatObjLogs, thisObjLogs, remainingObjSet \ {obj})
                            ELSE FindAckdWrites(thatObjLogs, thisObjLogs, remainingObjSet \ {obj})
                                                                             
\*        RECURSIVE AcceptBackpropLog(_, _)
\*        AcceptBackpropLog(thatLog, thisLog) ==  IF thisLog = << >> \* if this log is empty
\*                                                THEN << >> \* then nothing could have been backpropped, nothing changes
\*                                                ELSE    LET thisMostRecentVer == Head(thisLog)
\*                                                        IN  IF thisMostRecentVer.commitStatus = CLEAN \* if this log is clean
\*                                                            THEN thisLog \* then we have nothing to add
\*                                                            ELSE    LET thatMostRecentVer == Head(thatLog) \* if this log has dirty writes
\*                                                                    \* and the backpropped log has the same write
\*                                                                    IN  IF  thisMostRecentVer.uniqueId = thatMostRecentVer.uniqueId
\*                                                                        THEN    IF thatMostRecentVer.commitStatus = DIRTY \* and that log is also dirty
\*                                                                                THEN thisLog  \* the two logs match, nothing more to change
\*                                                                                \* if that log is clean though, commit the write in this log
\*                                                                                \* and keep comparing matches between the rest of that log and this log
\*                                                                                ELSE Cons(thatMostRecentVer, AcceptBackpropLog(Tail(thatLog), Tail(thisLog)))
\*                                                                        \* if that log has an earlier version, keep backtracking through this log
\*                                                                        ELSE Cons(thisMostRecentVer, AcceptBackpropLog(thatLog, Tail(thisLog)))
        
\*        RECURSIVE AcceptFwdpropLog(_, _)
\*        AcceptFwdpropLog(thatLog, thisLog) == IF thatLog = << >> \* if propagated log is empty
\*                                              THEN << >> \* then nothing propagated, return empty log
\*                                              ELSE  
    }
    
    \* macro definitions
    macro send(sender, receiver, msg) {
        msgQs[<<sender, receiver>>] := Append(@, msg)
    }
    
    macro failoverSend(sender, receiver, msg) {
        failoverMsgQs[<<sender, receiver>>] := Append(@, msg)
    }
    
    macro recv(sender, receiver, msg) {
        msg := Head(msgQs[<<sender, receiver>>]);
        msgQs[<<sender, receiver>>] := Tail(@);
    }
    
    macro failoverRecv(sender, receiver, msg) {
        msg := Head(failoverMsgQs[<<sender, receiver>>]);
        failoverMsgQs[<<sender, receiver>>] := Tail(@);
    }
    
    macro add(set, k, v) {
        set := set \cup {<<k, v>>};
    }
    
    macro remove(set, k) {
        set := set \ {FindPair(set, k)};
    }
    macro find(set, k, v) {
        v := CHOOSE kv \in set: kv[1] = k;
    }
    macro apportionQ(src, req) {
        send(src, tail, req);
    }
    
    macro write(node, objVer) {
        objLogs[node][objVer.obj] := Cons(objVer, @);
    }
    
    macro addToOpSet(reqOp) {
        if (reqOp.callType = WRITE_RESP) {
            allSubmittedWriteOps[reqOp.op.obj] := allSubmittedWriteOps[reqOp.op.obj] \cup {reqOp};
        } else {
            allSubmittedReadOps[reqOp.op.obj] := allSubmittedReadOps[reqOp.op.obj] \cup {reqOp};
        }
    }
    
    fair process(iclient = "initClient")
        variables   uninitializedObjs = Objects,
                    initObj = NullObj,
                    objs_init = Objects,
                    obj_init = NullObj,
                    actions_init = {WRITE_INV, READ_INV},
                    action_init = NullCall,
                    gateway_cinit = NullNode,
                    msg_cinit = NullReq,
                    uniqueId_cinit = <<initClient, 1>>,
                    sentOps_init = 0,
                    recvdOps_init = 0;
    {
\*        neverstart: when FALSE;
        initializeObj: while (uninitializedObjs /= {}) {
            initObj := CHOOSE o \in uninitializedObjs: TRUE;
            send(initClient, head, [callType |-> WRITE_INV,
                                    uniqueId |-> uniqueId_cinit,
                                    startTs |-> NullTs,
                                    commitTs |-> NullTs,
                                    op |-> [obj |-> initObj,
                                            uniqueId |-> uniqueId_cinit,
                                            writeStartTs |-> NullTs,
                                            writeCommitTs |-> NullTs,
                                            commitStatus |-> DIRTY]]);
            
            uninitializedObjs := uninitializedObjs \ {initObj};
            uniqueId_cinit := Increment(uniqueId_cinit);
            
            waitFor_init:
            when msgQs[<<head, initClient>>] /= << >>; 
            recv(head, initClient, msg_cinit); 
            addToOpSet(msg_cinit);
        };
        start := TRUE;
        
        concurrentOps_init: while (objs_init /= {}) {
            obj_init := CHOOSE o \in objs_init: TRUE;
            objs_init := objs_init \ {obj_init};
            actions_init := {WRITE_INV, READ_INV};
            
            readOrWrite_init: while (actions_init /= {}) {
                action_init := CHOOSE a \in actions_init: TRUE;
                actions_init := actions_init \ {action_init};
                
                send(initClient, head, [callType |-> action_init,
                                        uniqueId |-> uniqueId_cinit,
                                        startTs |-> NullTs,
                                        commitTs |-> NullTs,
                                        op |-> [obj |-> obj_init,
                                                uniqueId |-> uniqueId_cinit,
                                                writeStartTs |-> NullTs,
                                                writeCommitTs |-> NullTs,
                                                commitStatus |-> IF action_init = WRITE_INV 
                                                                    THEN DIRTY 
                                                                    ELSE NullCommitStatus]]);
                uniqueId_cinit := Increment(uniqueId_cinit);
                sentOps_init := sentOps_init + 1;
                
                waitForOps_init:
                while (recvdOps_init < sentOps_init) {
                    with (temp \in {s \in SendersTo(initClient): msgQs[<<s, initClient>>] /= << >>}) {
                        gateway_cinit := temp;
                    };
                    when msgQs[<<gateway_cinit, initClient>>] /= << >>; 
                    recv(gateway_cinit, initClient, msg_cinit);
                    addToOpSet(msg_cinit); 
                    recvdOps_init := recvdOps_init + 1;
                };
            };

        };   
        terminate_init: terminatedYet[initClient] := TRUE
    }
    
    fair process(crasher="crasher")
        variables crashNode = NullNode; 
    {
        waitForInit_crasher:
        when start = TRUE;
\*        when FALSE;
        initCrash:
        crashNode := CHOOSE n \in ActiveNodes: n /= currentHead /\ n /= currentTail;
        send(crasherClient, crashNode, [callType |-> CRASH]);
    }
    
    fair process(c \in nonInitClients)
        variables   objs = Objects,
                    obj = NullObj,
                    actions = {WRITE_INV, READ_INV},
                    action = NullCall,
                    gateway_c = NullNode,
                    msg_c = NullReq,
                    uniqueId = <<self, 1>>,
                    outstandingOps = 0
                    ;
    {   
        waitForInit: when start = TRUE;
        concurrentOps: 
        while (objs /= {}) {
            obj := CHOOSE o \in objs: TRUE;
            objs := objs \ {obj};
            
            actions := {WRITE_INV, READ_INV};
            readOrWrite: 
            while (actions /= {}) {
                action := CHOOSE a \in actions: TRUE;
                actions := actions \ {action};
                
                sendToActiveNode:
                while ( \/ msg_c = NullReq
                        \/ msg_c.callType = TIMEOUT) {
                    send(   self, 
                            IF action = WRITE_INV THEN head ELSE CHOOSE n \in ActiveNodes: n /= head, 
                            [   callType |-> action,
                                uniqueId |-> uniqueId,
                                startTs |-> NullTs,
                                commitTs |-> NullTs,
                                op |-> [obj |-> obj,
                                        uniqueId |-> uniqueId,
                                        writeStartTs |-> NullTs,
                                        writeCommitTs |-> NullTs,
                                        commitStatus |->    IF action = WRITE_INV 
                                                            THEN DIRTY 
                                                            ELSE NullCommitStatus]]);
                    outstandingOps := outstandingOps + 1;
                    
                    waitForOps:
                    while (outstandingOps > 0) {
                        with (temp \in {s \in SendersTo(self): msgQs[<<s, self>>] /= << >>}) {
                            gateway_c := temp;
                            outstandingOps := outstandingOps - 1;
                        };
                    };
                    when msgQs[<<gateway_c, self>>] /= << >>; 
                    recv(gateway_c, self, msg_c); 
                };
                
                uniqueId := Increment(uniqueId);
                addToOpSet(msg_c);
                assert(msg_c.uniqueId[1] = self);
                msg_c := NullReq;
            };
             
        };
        
        terminate: terminatedYet[self] := TRUE;
    }
    
    fair process(zk="zookeeper")
        variables   crashedNode = NullNode,
                    sender_zk = NullNode,
                    liveNode = NullNode,
                    req_z = NullReq,
                    liveNodes = {}; 
    {
        listen_z: while (TRUE) {
            with (temp \in {s \in SendersTo(Zookeeper): msgQs[<<s, Zookeeper>>] /= << >>}) {
                sender_zk := temp;
            };
            
            when msgQs[<<sender_zk, Zookeeper>>] /= << >>;
            recv(sender_zk, Zookeeper, req_z); 
            
            if (req_z.callType = ZK_SESSION_ENDED) {
                crashedNode := sender_zk;
                liveNodes := Nodes \ {crashedNode};
                triggerWatchesNodeDel:
                while (liveNodes /= {}) {
                    liveNode := CHOOSE ln \in liveNodes: TRUE;
                    send(Zookeeper, liveNode, [ callType    |-> ZK_NODE_DEL,
                                                crashedNode  |-> crashedNode]);
                    liveNodes := liveNodes \ {liveNode};
                }                        
            } else {
                if (req_z.callType = ZK_CREATE) {
                    liveNodes := Nodes;
                    triggerWatchesNodeAdd:
                    while (liveNodes /= {}) {
                        liveNode := CHOOSE ln \in liveNodes : TRUE;
                        failoverSend(Zookeeper, liveNode, [ callType |-> ZK_NODE_ADD]);
                        liveNodes := liveNodes \ {liveNode};
                    };
                    
                    liveNodes := Clients;
                    
                    timeoutClients:
                    while (liveNodes /= {}) {
                        liveNode := CHOOSE client \in liveNodes : TRUE;
                        liveNodes := liveNodes \ {liveNode};
                        
                        if (msgQs[<<liveNode, crashedNode>>] /= << >>) {
                            send(Zookeeper, liveNode, [callType |-> TIMEOUT]);
                        };
                    };
                }
            }
        }
    }
    
    fair process(n \in Nodes) 
        variables   role = MID,
                    sender = NullNode,
                    req = NullReq,
                    pendingInvos = {},
                    failoverPendingInvos = {},
                    now = timeOracle,
                    failoverUnpropagatedWrites = {},
                    failoverAckdWrites = {},
                    version = NullObjectVersion,
                    pendingInvo = <<NullUniqueId, NullNode>>
                    ;
                    
    {
        roleAssignment:
        role := CASE self = head -> HEAD
                [] self = tail -> TAIL
                [] OTHER -> MID;
                
        listen:
        while (TRUE) {
            with (temp \in {s \in SendersTo(self): msgQs[<<s, self>>] /= << >>}) {
                sender := temp;
            };
                
            when msgQs[<<sender, self>>] /= << >>;  
            recv(sender, self, req);
            if (role = HEAD) { 
                if (req.callType = READ_INV) {
                    goto handleReadInv;
                } else {
                    if (req.callType = READ_RESP) {
                        goto handleReadResp;
                    } else {
                        if (req.callType = WRITE_INV) {
                            goto handleWriteInvHead;
                        } else {
                            if (req.callType = WRITE_RESP) {
                                goto handleWriteResp;
                            } else {
                                if (req.callType = CRASH) {
                                    goto crash;
                                } else {
                                    if (req.callType = ZK_NODE_DEL) {
                                        if (req.crashedNode = Successors[self]) {
                                            goto failoverCrashedNodeIsSuccessor;
                                        } else {
                                            if (req.crashedNode = Predecessors[self]) {
                                                goto failoverCrashedNodeIsPredecessor; 
                                            } else {
                                                goto failoverListen;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            } else {
                if (role = TAIL) {
                    if (req.callType = READ_INV) {
                        goto handleReadInvTail;
                    } else {
                        if (req.callType = WRITE_INV) {
                            goto handleWriteInvTail;
                        } else {
                            if (req.callType = CRASH) {
                                goto crash;
                            } else {
                                if (req.callType = ZK_NODE_DEL) {
                                    if (Predecessors[self] = req.crashedNode) {
                                        goto failoverCrashedNodeIsPredecessor;
                                    } else {
                                        goto failoverListen;
                                    }
                                }
                            } 
                        }
                    }
                } else {
                    if (req.callType = READ_INV) {
                        goto handleReadInv;
                    } else {
                        if (req.callType = READ_RESP) {
                            goto handleReadResp;
                        } else {
                            if (req.callType = WRITE_INV) {
                                goto handleWriteInv;
                            } else {
                                if (req.callType = WRITE_RESP) {
                                    goto handleWriteResp;
                                } else {
                                    if (req.callType = CRASH){
                                        goto crash;
                                    } else {
                                        if (req.callType = ZK_NODE_DEL) {
                                            if (req.crashedNode = Successors[self]) {
                                                goto failoverCrashedNodeIsSuccessor;
                                            } else {
                                                if (req.crashedNode = Predecessors[self]) {
                                                    goto failoverCrashedNodeIsPredecessor; 
                                                } else {
                                                    goto failoverListen;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        };
        
        failoverListen:
        while (TRUE) {
            with (temp \in {s \in SendersTo(self): failoverMsgQs[<<s, self>>] /= << >>}) {
                sender := temp;
            };
            
            when failoverMsgQs[<<sender, self>>] /= << >>;  
            failoverRecv(sender, self, req);
            
            if (req.callType = FAILOVER_NOTIFY_TAIL) {
                if (role = TAIL) {
                    goto failoverTailPropsLog;
                }
            } else {
                if (req.callType = FAILOVER_PROPAGATE_LOG) {
                    goto failoverAssumeNewTail;
                } else {
                    if (req.callType = ZK_NODE_ADD) {
                        goto listen;
                    }
                }
            }
            
        };
        
        \********
        \* handle read invocation requests
        \********
        handleReadInv:
        if (IsDirty(self, req.op.obj)) {
            apportionQ: send(self, currentTail, req);
            add(pendingInvos, req.uniqueId, sender);
        } else {
            now := timeOracle;
            timeOracle := timeOracle + 1;
            req := [    callType    |-> READ_RESP,
                        uniqueId    |-> req.uniqueId,
                        startTs     |-> now,
                        commitTs    |-> now,
                        op          |-> Read(self, req.op.obj)];
            send(self, sender, req);
        };
        
        finishReadInv:
        goto listen;
        
        \********
        \* handle read invocations at the tail
        \********
        handleReadInvTail:
        now := timeOracle;
        timeOracle := timeOracle + 1;
        req := [ callType |-> READ_RESP,
                 uniqueId |-> req.uniqueId,
                 startTs |-> now,
                 commitTs |-> now,
                 op |-> Read(self, req.op.obj)];
        send(self, sender, req);
        
        finishReadInvTail:
        goto listen;
        
        \********
        \* handle read responses
        \********
        handleReadResp:
        send(self, Find(pendingInvos, req.uniqueId), req);
        remove(pendingInvos, req.uniqueId);
        finishReadResp:
        goto listen;
        
        \********
        \* handle write invocations at the head
        \********
        handleWriteInvHead:
        now := timeOracle;
        timeOracle := timeOracle + 1;
        req := [req EXCEPT  !.startTs = now,
                            !.op.writeStartTs = now,
                            !.op.commitStatus = DIRTY];
        write(self, req.op);
        send(self, Successors[self], req);
        add(pendingInvos, req.uniqueId, sender);
        
        finishWriteInvHead:
        goto listen;
        
        \********
        \* handle write invocations
        \********
        handleWriteInv:
        write(self, req.op);
        send(self, Successors[self], req);
        add(pendingInvos, req.uniqueId, sender);
        
        finishWriteInv:
        goto listen;
        
        \********
        \* handle write invocations at the tail
        \********
        handleWriteInvTail:
        now := timeOracle;
        timeOracle := timeOracle + 1;
        write(self, [req.op EXCEPT  !.writeCommitTs = now, 
                                    !.commitStatus = CLEAN]);
        tailAck: req := [   callType |-> WRITE_RESP,
                            uniqueId |-> req.uniqueId,
                            startTs  |-> req.startTs,
                            commitTs |-> Read(self, req.op.obj).writeCommitTs,
                            op |-> Read(self, req.op.obj)];
        send(self, Predecessors[self], req);
        
        finishWriteInvTail:
        goto listen;
        
        \********
        \* handle write response
        \********
        handleWriteResp:
        objLogs[self][req.op.obj] := CommitDirtyVersion(@, req.op);
        send(self, Find(pendingInvos, req.uniqueId), req);
        remove(pendingInvos, req.uniqueId);
        
        finishWriteResp:
        goto listen;
        
        \********
        \* failover, if the crashed node is this node's successor
        \********
        failoverCrashedNodeIsSuccessor:
        failoverSend(self, Successors[Successors[self]], [  callType |-> FAILOVER_PROPAGATE_LOG,
                                                            log |-> objLogs[self]
                                                          ]);
        Successors[self] := Successors[Successors[self]];
        finishCrashedNodeIsSuccessor:
        goto failoverListen;
        
        \********
        \* failover, if crashed node is this node's predecessor
        \********
        failoverCrashedNodeIsPredecessor:
        \* wait for propagate message
        with (temp \in {s \in SendersTo(self): failoverMsgQs[<<s, self>>] /= << >>}) {
            sender := temp;
        };
        when failoverMsgQs[<<sender, self>>] /= << >>;  
        failoverRecv(sender, self, req);
        assert(req.callType = FAILOVER_PROPAGATE_LOG);
        
        
        failoverUnpropagatedWrites := FindUnpropagatedWrites(req.log, objLogs[self], Objects);
        propagateFailedWrites:
        while (failoverUnpropagatedWrites /= {}) {
            version := CHOOSE v \in failoverUnpropagatedWrites : TRUE;
            write(self, version);
            send(self, Successors[self], [  callType |-> WRITE_INV,
                                            uniqueId |-> version.uniqueId,
                                            startTs |-> version.writeStartTs,
                                            commitTs |-> NullTs,
                                            op |-> version]);
            add(pendingInvos, version.uniqueId, sender);
            failoverUnpropagatedWrites := failoverUnpropagatedWrites \ {version};
        };
        failoverAckdWrites := FindAckdWrites(req.log, objLogs[self], Objects);
        
        backpropFailedAcks:
        while (failoverAckdWrites /= {}) {
            version := CHOOSE v \in failoverAckdWrites : TRUE;
            send(self, Predecessors[Predecessors[self]], [  callType |-> WRITE_RESP,
                                                            uniqueId |-> version.uniqueId,
                                                            startTs |-> version.writeStartTs,
                                                            commitTs |-> version.writeCommitTs,
                                                            op |-> version]);
        };
        
        notifyTail:
        failoverSend(self, currentTail, [callType |-> FAILOVER_NOTIFY_TAIL]);
        
        Predecessors[self] := Predecessors[Predecessors[self]];
        
        finishCrashedNodeIsPredecessor:
        goto failoverListen;
        
        \********
        \* failover, tail propagates log to new tail
        \********
        failoverTailPropsLog:
        failoverSend(self, Successors[self], [  callType |-> FAILOVER_PROPAGATE_LOG,
                                                log |-> objLogs[self]
                                              ]);
        finishFailoverTailPropsLog:
        goto failoverListen;
        
        \********
        \* failover, assume new tail role
        \********
        failoverAssumeNewTail:
        objLogs[self] := req.log;
        currentTail := self;
        
        notifyZookeeper:
        send(self, Zookeeper, [ callType |-> ZK_CREATE]);

        finishFailoverAssumeNewTail:
        goto failoverListen;
        
        
        \********
        \* crash a node
        \********
        crash:
        send(self, Zookeeper, [ callType |-> ZK_SESSION_ENDED]);
        
        zkConfigChanged:
        with (temp \in {s \in SendersTo(self): failoverMsgQs[<<s, self>>] /= << >>}) {
                sender:= temp;
        };
        when failoverMsgQs[<<sender, self>>] /= << >>;  
        failoverRecv(sender, self, req);
        assert(req.callType = ZK_NODE_ADD);
        
        
    }
    
}

****************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "85bb0e45" /\ chksum(tla) = "dc975353")
VARIABLES msgQs, failoverMsgQs, objLogs, allSubmittedWriteOps, 
          allSubmittedReadOps, terminatedYet, nonInitClients, start, 
          timeOracle, Successors, Predecessors, currentHead, currentTail, pc

(* define statement *)
RECURSIVE CommitDirtyVersion(_, _)
CommitDirtyVersion(objLog, committedVer) == LET mostRecentVer == Head(objLog)
                                                uniqueId == committedVer.uniqueId
                                                writeCommitTs == committedVer.writeCommitTs
                                            IN  IF mostRecentVer.uniqueId = uniqueId
                                                THEN Cons([mostRecentVer EXCEPT !.commitStatus = CLEAN,
                                                                                !.writeCommitTs = writeCommitTs],
                                                           Tail(objLog))
                                                ELSE Cons(mostRecentVer, CommitDirtyVersion(Tail(objLog), committedVer))

IsDirty(node, obj) == Head(objLogs[node][obj]).commitStatus = DIRTY
Read(node, obj) == Head(objLogs[node][obj])
FindPair(set, k) == CHOOSE kv \in set: kv[1] = k
Find(set, k) == LET kv == FindPair(set, k) IN kv[2]

Increment(id) == <<id[1], id[2]+1>>

RECURSIVE FindActiveNodes(_)
FindActiveNodes(node) ==    IF node = currentTail
                        THEN {node}
                        ELSE {node} \cup FindActiveNodes(Successors[node])

ActiveNodes == FindActiveNodes(currentHead)

RECURSIVE FindUnpropagatedWrites(_, _, _)
FindUnpropagatedWrites(thatObjLogs, thisObjLogs, remainingObjSet) ==
    IF remainingObjSet = {}
    THEN {}
    ELSE    LET obj == CHOOSE o \in remainingObjSet : TRUE
            IN  LET thatLog == thatObjLogs[obj]
                    thisLog == thisObjLogs[obj]
                IN  IF  /\ Head(thatLog).commitStatus = DIRTY
                        /\ Head(thisLog).commitStatus = CLEAN
                        /\ Head(thatLog).uniqueId /= Head(thisLog).uniqueId
                    THEN {Head(thatLog)} \cup FindUnpropagatedWrites(thatObjLogs, thisObjLogs, remainingObjSet \ {obj})
                    ELSE FindUnpropagatedWrites(thatObjLogs, thisObjLogs, remainingObjSet \ {obj})

RECURSIVE FindAckdWrites(_, _, _)
FindAckdWrites(thatObjLogs, thisObjLogs, remainingObjSet) ==
    IF remainingObjSet = {}
    THEN {}
    ELSE    LET obj == CHOOSE o \in remainingObjSet : TRUE
            IN LET  thatLog == thatObjLogs[obj]
                    thisLog == thisObjLogs[obj]
               IN   IF  /\ Head(thatLog).uniqueId = Head(thisLog).uniqueId
                        /\ Head(thatLog).commitStatus = DIRTY
                        /\ Head(thisLog).commitStatus = CLEAN
                    THEN {Head(thisLog)} \cup FindAckdWrites(thatObjLogs, thisObjLogs, remainingObjSet \ {obj})
                    ELSE FindAckdWrites(thatObjLogs, thisObjLogs, remainingObjSet \ {obj})

VARIABLES uninitializedObjs, initObj, objs_init, obj_init, actions_init, 
          action_init, gateway_cinit, msg_cinit, uniqueId_cinit, sentOps_init, 
          recvdOps_init, crashNode, objs, obj, actions, action, gateway_c, 
          msg_c, uniqueId, outstandingOps, crashedNode, sender_zk, liveNode, 
          req_z, liveNodes, role, sender, req, pendingInvos, 
          failoverPendingInvos, now, failoverUnpropagatedWrites, 
          failoverAckdWrites, version, pendingInvo

vars == << msgQs, failoverMsgQs, objLogs, allSubmittedWriteOps, 
           allSubmittedReadOps, terminatedYet, nonInitClients, start, 
           timeOracle, Successors, Predecessors, currentHead, currentTail, pc, 
           uninitializedObjs, initObj, objs_init, obj_init, actions_init, 
           action_init, gateway_cinit, msg_cinit, uniqueId_cinit, 
           sentOps_init, recvdOps_init, crashNode, objs, obj, actions, action, 
           gateway_c, msg_c, uniqueId, outstandingOps, crashedNode, sender_zk, 
           liveNode, req_z, liveNodes, role, sender, req, pendingInvos, 
           failoverPendingInvos, now, failoverUnpropagatedWrites, 
           failoverAckdWrites, version, pendingInvo >>

ProcSet == {"initClient"} \cup {"crasher"} \cup (nonInitClients) \cup {"zookeeper"} \cup (Nodes)

Init == (* Global variables *)
        /\ msgQs = [edge \in Network |-> << >>]
        /\ failoverMsgQs = [edge \in Network |-> << >>]
        /\ objLogs = [n \in Nodes |-> [o \in Objects |-> << >>]]
        /\ allSubmittedWriteOps = [o \in Objects |-> {}]
        /\ allSubmittedReadOps = [ o \in Objects |-> {}]
        /\ terminatedYet = [c \in Clients |-> FALSE]
        /\ nonInitClients = Clients \ {initClient}
        /\ start = FALSE
        /\ timeOracle = 10
        /\ Successors = [n \in Nodes |-> LET e == CHOOSE edge \in NextEdges : edge[1] = n IN e[2]]
        /\ Predecessors = [n \in Nodes |-> LET e == CHOOSE edge \in PrevEdges : edge[1] = n IN e[2]]
        /\ currentHead = head
        /\ currentTail = tail
        (* Process iclient *)
        /\ uninitializedObjs = Objects
        /\ initObj = NullObj
        /\ objs_init = Objects
        /\ obj_init = NullObj
        /\ actions_init = {WRITE_INV, READ_INV}
        /\ action_init = NullCall
        /\ gateway_cinit = NullNode
        /\ msg_cinit = NullReq
        /\ uniqueId_cinit = <<initClient, 1>>
        /\ sentOps_init = 0
        /\ recvdOps_init = 0
        (* Process crasher *)
        /\ crashNode = NullNode
        (* Process c *)
        /\ objs = [self \in nonInitClients |-> Objects]
        /\ obj = [self \in nonInitClients |-> NullObj]
        /\ actions = [self \in nonInitClients |-> {WRITE_INV, READ_INV}]
        /\ action = [self \in nonInitClients |-> NullCall]
        /\ gateway_c = [self \in nonInitClients |-> NullNode]
        /\ msg_c = [self \in nonInitClients |-> NullReq]
        /\ uniqueId = [self \in nonInitClients |-> <<self, 1>>]
        /\ outstandingOps = [self \in nonInitClients |-> 0]
        (* Process zk *)
        /\ crashedNode = NullNode
        /\ sender_zk = NullNode
        /\ liveNode = NullNode
        /\ req_z = NullReq
        /\ liveNodes = {}
        (* Process n *)
        /\ role = [self \in Nodes |-> MID]
        /\ sender = [self \in Nodes |-> NullNode]
        /\ req = [self \in Nodes |-> NullReq]
        /\ pendingInvos = [self \in Nodes |-> {}]
        /\ failoverPendingInvos = [self \in Nodes |-> {}]
        /\ now = [self \in Nodes |-> timeOracle]
        /\ failoverUnpropagatedWrites = [self \in Nodes |-> {}]
        /\ failoverAckdWrites = [self \in Nodes |-> {}]
        /\ version = [self \in Nodes |-> NullObjectVersion]
        /\ pendingInvo = [self \in Nodes |-> <<NullUniqueId, NullNode>>]
        /\ pc = [self \in ProcSet |-> CASE self = "initClient" -> "initializeObj"
                                        [] self = "crasher" -> "waitForInit_crasher"
                                        [] self \in nonInitClients -> "waitForInit"
                                        [] self = "zookeeper" -> "listen_z"
                                        [] self \in Nodes -> "roleAssignment"]

initializeObj == /\ pc["initClient"] = "initializeObj"
                 /\ IF uninitializedObjs /= {}
                       THEN /\ initObj' = (CHOOSE o \in uninitializedObjs: TRUE)
                            /\ msgQs' = [msgQs EXCEPT ![<<initClient, head>>] = Append(@, ([callType |-> WRITE_INV,
                                                                                            uniqueId |-> uniqueId_cinit,
                                                                                            startTs |-> NullTs,
                                                                                            commitTs |-> NullTs,
                                                                                            op |-> [obj |-> initObj',
                                                                                                    uniqueId |-> uniqueId_cinit,
                                                                                                    writeStartTs |-> NullTs,
                                                                                                    writeCommitTs |-> NullTs,
                                                                                                    commitStatus |-> DIRTY]]))]
                            /\ uninitializedObjs' = uninitializedObjs \ {initObj'}
                            /\ uniqueId_cinit' = Increment(uniqueId_cinit)
                            /\ pc' = [pc EXCEPT !["initClient"] = "waitFor_init"]
                            /\ start' = start
                       ELSE /\ start' = TRUE
                            /\ pc' = [pc EXCEPT !["initClient"] = "concurrentOps_init"]
                            /\ UNCHANGED << msgQs, uninitializedObjs, initObj, 
                                            uniqueId_cinit >>
                 /\ UNCHANGED << failoverMsgQs, objLogs, allSubmittedWriteOps, 
                                 allSubmittedReadOps, terminatedYet, 
                                 nonInitClients, timeOracle, Successors, 
                                 Predecessors, currentHead, currentTail, 
                                 objs_init, obj_init, actions_init, 
                                 action_init, gateway_cinit, msg_cinit, 
                                 sentOps_init, recvdOps_init, crashNode, objs, 
                                 obj, actions, action, gateway_c, msg_c, 
                                 uniqueId, outstandingOps, crashedNode, 
                                 sender_zk, liveNode, req_z, liveNodes, role, 
                                 sender, req, pendingInvos, 
                                 failoverPendingInvos, now, 
                                 failoverUnpropagatedWrites, 
                                 failoverAckdWrites, version, pendingInvo >>

waitFor_init == /\ pc["initClient"] = "waitFor_init"
                /\ msgQs[<<head, initClient>>] /= << >>
                /\ msg_cinit' = Head(msgQs[<<head, initClient>>])
                /\ msgQs' = [msgQs EXCEPT ![<<head, initClient>>] = Tail(@)]
                /\ IF msg_cinit'.callType = WRITE_RESP
                      THEN /\ allSubmittedWriteOps' = [allSubmittedWriteOps EXCEPT ![msg_cinit'.op.obj] = allSubmittedWriteOps[msg_cinit'.op.obj] \cup {msg_cinit'}]
                           /\ UNCHANGED allSubmittedReadOps
                      ELSE /\ allSubmittedReadOps' = [allSubmittedReadOps EXCEPT ![msg_cinit'.op.obj] = allSubmittedReadOps[msg_cinit'.op.obj] \cup {msg_cinit'}]
                           /\ UNCHANGED allSubmittedWriteOps
                /\ pc' = [pc EXCEPT !["initClient"] = "initializeObj"]
                /\ UNCHANGED << failoverMsgQs, objLogs, terminatedYet, 
                                nonInitClients, start, timeOracle, Successors, 
                                Predecessors, currentHead, currentTail, 
                                uninitializedObjs, initObj, objs_init, 
                                obj_init, actions_init, action_init, 
                                gateway_cinit, uniqueId_cinit, sentOps_init, 
                                recvdOps_init, crashNode, objs, obj, actions, 
                                action, gateway_c, msg_c, uniqueId, 
                                outstandingOps, crashedNode, sender_zk, 
                                liveNode, req_z, liveNodes, role, sender, req, 
                                pendingInvos, failoverPendingInvos, now, 
                                failoverUnpropagatedWrites, failoverAckdWrites, 
                                version, pendingInvo >>

concurrentOps_init == /\ pc["initClient"] = "concurrentOps_init"
                      /\ IF objs_init /= {}
                            THEN /\ obj_init' = (CHOOSE o \in objs_init: TRUE)
                                 /\ objs_init' = objs_init \ {obj_init'}
                                 /\ actions_init' = {WRITE_INV, READ_INV}
                                 /\ pc' = [pc EXCEPT !["initClient"] = "readOrWrite_init"]
                            ELSE /\ pc' = [pc EXCEPT !["initClient"] = "terminate_init"]
                                 /\ UNCHANGED << objs_init, obj_init, 
                                                 actions_init >>
                      /\ UNCHANGED << msgQs, failoverMsgQs, objLogs, 
                                      allSubmittedWriteOps, 
                                      allSubmittedReadOps, terminatedYet, 
                                      nonInitClients, start, timeOracle, 
                                      Successors, Predecessors, currentHead, 
                                      currentTail, uninitializedObjs, initObj, 
                                      action_init, gateway_cinit, msg_cinit, 
                                      uniqueId_cinit, sentOps_init, 
                                      recvdOps_init, crashNode, objs, obj, 
                                      actions, action, gateway_c, msg_c, 
                                      uniqueId, outstandingOps, crashedNode, 
                                      sender_zk, liveNode, req_z, liveNodes, 
                                      role, sender, req, pendingInvos, 
                                      failoverPendingInvos, now, 
                                      failoverUnpropagatedWrites, 
                                      failoverAckdWrites, version, pendingInvo >>

readOrWrite_init == /\ pc["initClient"] = "readOrWrite_init"
                    /\ IF actions_init /= {}
                          THEN /\ action_init' = (CHOOSE a \in actions_init: TRUE)
                               /\ actions_init' = actions_init \ {action_init'}
                               /\ msgQs' = [msgQs EXCEPT ![<<initClient, head>>] = Append(@, ([callType |-> action_init',
                                                                                               uniqueId |-> uniqueId_cinit,
                                                                                               startTs |-> NullTs,
                                                                                               commitTs |-> NullTs,
                                                                                               op |-> [obj |-> obj_init,
                                                                                                       uniqueId |-> uniqueId_cinit,
                                                                                                       writeStartTs |-> NullTs,
                                                                                                       writeCommitTs |-> NullTs,
                                                                                                       commitStatus |-> IF action_init' = WRITE_INV
                                                                                                                           THEN DIRTY
                                                                                                                           ELSE NullCommitStatus]]))]
                               /\ uniqueId_cinit' = Increment(uniqueId_cinit)
                               /\ sentOps_init' = sentOps_init + 1
                               /\ pc' = [pc EXCEPT !["initClient"] = "waitForOps_init"]
                          ELSE /\ pc' = [pc EXCEPT !["initClient"] = "concurrentOps_init"]
                               /\ UNCHANGED << msgQs, actions_init, 
                                               action_init, uniqueId_cinit, 
                                               sentOps_init >>
                    /\ UNCHANGED << failoverMsgQs, objLogs, 
                                    allSubmittedWriteOps, allSubmittedReadOps, 
                                    terminatedYet, nonInitClients, start, 
                                    timeOracle, Successors, Predecessors, 
                                    currentHead, currentTail, 
                                    uninitializedObjs, initObj, objs_init, 
                                    obj_init, gateway_cinit, msg_cinit, 
                                    recvdOps_init, crashNode, objs, obj, 
                                    actions, action, gateway_c, msg_c, 
                                    uniqueId, outstandingOps, crashedNode, 
                                    sender_zk, liveNode, req_z, liveNodes, 
                                    role, sender, req, pendingInvos, 
                                    failoverPendingInvos, now, 
                                    failoverUnpropagatedWrites, 
                                    failoverAckdWrites, version, pendingInvo >>

waitForOps_init == /\ pc["initClient"] = "waitForOps_init"
                   /\ IF recvdOps_init < sentOps_init
                         THEN /\ \E temp \in {s \in SendersTo(initClient): msgQs[<<s, initClient>>] /= << >>}:
                                   gateway_cinit' = temp
                              /\ msgQs[<<gateway_cinit', initClient>>] /= << >>
                              /\ msg_cinit' = Head(msgQs[<<gateway_cinit', initClient>>])
                              /\ msgQs' = [msgQs EXCEPT ![<<gateway_cinit', initClient>>] = Tail(@)]
                              /\ IF msg_cinit'.callType = WRITE_RESP
                                    THEN /\ allSubmittedWriteOps' = [allSubmittedWriteOps EXCEPT ![msg_cinit'.op.obj] = allSubmittedWriteOps[msg_cinit'.op.obj] \cup {msg_cinit'}]
                                         /\ UNCHANGED allSubmittedReadOps
                                    ELSE /\ allSubmittedReadOps' = [allSubmittedReadOps EXCEPT ![msg_cinit'.op.obj] = allSubmittedReadOps[msg_cinit'.op.obj] \cup {msg_cinit'}]
                                         /\ UNCHANGED allSubmittedWriteOps
                              /\ recvdOps_init' = recvdOps_init + 1
                              /\ pc' = [pc EXCEPT !["initClient"] = "waitForOps_init"]
                         ELSE /\ pc' = [pc EXCEPT !["initClient"] = "readOrWrite_init"]
                              /\ UNCHANGED << msgQs, allSubmittedWriteOps, 
                                              allSubmittedReadOps, 
                                              gateway_cinit, msg_cinit, 
                                              recvdOps_init >>
                   /\ UNCHANGED << failoverMsgQs, objLogs, terminatedYet, 
                                   nonInitClients, start, timeOracle, 
                                   Successors, Predecessors, currentHead, 
                                   currentTail, uninitializedObjs, initObj, 
                                   objs_init, obj_init, actions_init, 
                                   action_init, uniqueId_cinit, sentOps_init, 
                                   crashNode, objs, obj, actions, action, 
                                   gateway_c, msg_c, uniqueId, outstandingOps, 
                                   crashedNode, sender_zk, liveNode, req_z, 
                                   liveNodes, role, sender, req, pendingInvos, 
                                   failoverPendingInvos, now, 
                                   failoverUnpropagatedWrites, 
                                   failoverAckdWrites, version, pendingInvo >>

terminate_init == /\ pc["initClient"] = "terminate_init"
                  /\ terminatedYet' = [terminatedYet EXCEPT ![initClient] = TRUE]
                  /\ pc' = [pc EXCEPT !["initClient"] = "Done"]
                  /\ UNCHANGED << msgQs, failoverMsgQs, objLogs, 
                                  allSubmittedWriteOps, allSubmittedReadOps, 
                                  nonInitClients, start, timeOracle, 
                                  Successors, Predecessors, currentHead, 
                                  currentTail, uninitializedObjs, initObj, 
                                  objs_init, obj_init, actions_init, 
                                  action_init, gateway_cinit, msg_cinit, 
                                  uniqueId_cinit, sentOps_init, recvdOps_init, 
                                  crashNode, objs, obj, actions, action, 
                                  gateway_c, msg_c, uniqueId, outstandingOps, 
                                  crashedNode, sender_zk, liveNode, req_z, 
                                  liveNodes, role, sender, req, pendingInvos, 
                                  failoverPendingInvos, now, 
                                  failoverUnpropagatedWrites, 
                                  failoverAckdWrites, version, pendingInvo >>

iclient == initializeObj \/ waitFor_init \/ concurrentOps_init
              \/ readOrWrite_init \/ waitForOps_init \/ terminate_init

waitForInit_crasher == /\ pc["crasher"] = "waitForInit_crasher"
                       /\ start = TRUE
                       /\ pc' = [pc EXCEPT !["crasher"] = "initCrash"]
                       /\ UNCHANGED << msgQs, failoverMsgQs, objLogs, 
                                       allSubmittedWriteOps, 
                                       allSubmittedReadOps, terminatedYet, 
                                       nonInitClients, start, timeOracle, 
                                       Successors, Predecessors, currentHead, 
                                       currentTail, uninitializedObjs, initObj, 
                                       objs_init, obj_init, actions_init, 
                                       action_init, gateway_cinit, msg_cinit, 
                                       uniqueId_cinit, sentOps_init, 
                                       recvdOps_init, crashNode, objs, obj, 
                                       actions, action, gateway_c, msg_c, 
                                       uniqueId, outstandingOps, crashedNode, 
                                       sender_zk, liveNode, req_z, liveNodes, 
                                       role, sender, req, pendingInvos, 
                                       failoverPendingInvos, now, 
                                       failoverUnpropagatedWrites, 
                                       failoverAckdWrites, version, 
                                       pendingInvo >>

initCrash == /\ pc["crasher"] = "initCrash"
             /\ crashNode' = (CHOOSE n \in ActiveNodes: n /= currentHead /\ n /= currentTail)
             /\ msgQs' = [msgQs EXCEPT ![<<crasherClient, crashNode'>>] = Append(@, ([callType |-> CRASH]))]
             /\ pc' = [pc EXCEPT !["crasher"] = "Done"]
             /\ UNCHANGED << failoverMsgQs, objLogs, allSubmittedWriteOps, 
                             allSubmittedReadOps, terminatedYet, 
                             nonInitClients, start, timeOracle, Successors, 
                             Predecessors, currentHead, currentTail, 
                             uninitializedObjs, initObj, objs_init, obj_init, 
                             actions_init, action_init, gateway_cinit, 
                             msg_cinit, uniqueId_cinit, sentOps_init, 
                             recvdOps_init, objs, obj, actions, action, 
                             gateway_c, msg_c, uniqueId, outstandingOps, 
                             crashedNode, sender_zk, liveNode, req_z, 
                             liveNodes, role, sender, req, pendingInvos, 
                             failoverPendingInvos, now, 
                             failoverUnpropagatedWrites, failoverAckdWrites, 
                             version, pendingInvo >>

crasher == waitForInit_crasher \/ initCrash

waitForInit(self) == /\ pc[self] = "waitForInit"
                     /\ start = TRUE
                     /\ pc' = [pc EXCEPT ![self] = "concurrentOps"]
                     /\ UNCHANGED << msgQs, failoverMsgQs, objLogs, 
                                     allSubmittedWriteOps, allSubmittedReadOps, 
                                     terminatedYet, nonInitClients, start, 
                                     timeOracle, Successors, Predecessors, 
                                     currentHead, currentTail, 
                                     uninitializedObjs, initObj, objs_init, 
                                     obj_init, actions_init, action_init, 
                                     gateway_cinit, msg_cinit, uniqueId_cinit, 
                                     sentOps_init, recvdOps_init, crashNode, 
                                     objs, obj, actions, action, gateway_c, 
                                     msg_c, uniqueId, outstandingOps, 
                                     crashedNode, sender_zk, liveNode, req_z, 
                                     liveNodes, role, sender, req, 
                                     pendingInvos, failoverPendingInvos, now, 
                                     failoverUnpropagatedWrites, 
                                     failoverAckdWrites, version, pendingInvo >>

concurrentOps(self) == /\ pc[self] = "concurrentOps"
                       /\ IF objs[self] /= {}
                             THEN /\ obj' = [obj EXCEPT ![self] = CHOOSE o \in objs[self]: TRUE]
                                  /\ objs' = [objs EXCEPT ![self] = objs[self] \ {obj'[self]}]
                                  /\ actions' = [actions EXCEPT ![self] = {WRITE_INV, READ_INV}]
                                  /\ pc' = [pc EXCEPT ![self] = "readOrWrite"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "terminate"]
                                  /\ UNCHANGED << objs, obj, actions >>
                       /\ UNCHANGED << msgQs, failoverMsgQs, objLogs, 
                                       allSubmittedWriteOps, 
                                       allSubmittedReadOps, terminatedYet, 
                                       nonInitClients, start, timeOracle, 
                                       Successors, Predecessors, currentHead, 
                                       currentTail, uninitializedObjs, initObj, 
                                       objs_init, obj_init, actions_init, 
                                       action_init, gateway_cinit, msg_cinit, 
                                       uniqueId_cinit, sentOps_init, 
                                       recvdOps_init, crashNode, action, 
                                       gateway_c, msg_c, uniqueId, 
                                       outstandingOps, crashedNode, sender_zk, 
                                       liveNode, req_z, liveNodes, role, 
                                       sender, req, pendingInvos, 
                                       failoverPendingInvos, now, 
                                       failoverUnpropagatedWrites, 
                                       failoverAckdWrites, version, 
                                       pendingInvo >>

readOrWrite(self) == /\ pc[self] = "readOrWrite"
                     /\ IF actions[self] /= {}
                           THEN /\ action' = [action EXCEPT ![self] = CHOOSE a \in actions[self]: TRUE]
                                /\ actions' = [actions EXCEPT ![self] = actions[self] \ {action'[self]}]
                                /\ pc' = [pc EXCEPT ![self] = "sendToActiveNode"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "concurrentOps"]
                                /\ UNCHANGED << actions, action >>
                     /\ UNCHANGED << msgQs, failoverMsgQs, objLogs, 
                                     allSubmittedWriteOps, allSubmittedReadOps, 
                                     terminatedYet, nonInitClients, start, 
                                     timeOracle, Successors, Predecessors, 
                                     currentHead, currentTail, 
                                     uninitializedObjs, initObj, objs_init, 
                                     obj_init, actions_init, action_init, 
                                     gateway_cinit, msg_cinit, uniqueId_cinit, 
                                     sentOps_init, recvdOps_init, crashNode, 
                                     objs, obj, gateway_c, msg_c, uniqueId, 
                                     outstandingOps, crashedNode, sender_zk, 
                                     liveNode, req_z, liveNodes, role, sender, 
                                     req, pendingInvos, failoverPendingInvos, 
                                     now, failoverUnpropagatedWrites, 
                                     failoverAckdWrites, version, pendingInvo >>

sendToActiveNode(self) == /\ pc[self] = "sendToActiveNode"
                          /\ IF \/ msg_c[self] = NullReq
                                \/ msg_c[self].callType = TIMEOUT
                                THEN /\ msgQs' = [msgQs EXCEPT ![<<self, (IF action[self] = WRITE_INV THEN head ELSE CHOOSE n \in ActiveNodes: n /= head)>>] = Append(@, ([   callType |-> action[self],
                                                                                                                                                                              uniqueId |-> uniqueId[self],
                                                                                                                                                                              startTs |-> NullTs,
                                                                                                                                                                              commitTs |-> NullTs,
                                                                                                                                                                              op |-> [obj |-> obj[self],
                                                                                                                                                                                      uniqueId |-> uniqueId[self],
                                                                                                                                                                                      writeStartTs |-> NullTs,
                                                                                                                                                                                      writeCommitTs |-> NullTs,
                                                                                                                                                                                      commitStatus |->    IF action[self] = WRITE_INV
                                                                                                                                                                                                          THEN DIRTY
                                                                                                                                                                                                          ELSE NullCommitStatus]]))]
                                     /\ outstandingOps' = [outstandingOps EXCEPT ![self] = outstandingOps[self] + 1]
                                     /\ pc' = [pc EXCEPT ![self] = "waitForOps"]
                                     /\ UNCHANGED << allSubmittedWriteOps, 
                                                     allSubmittedReadOps, 
                                                     msg_c, uniqueId >>
                                ELSE /\ uniqueId' = [uniqueId EXCEPT ![self] = Increment(uniqueId[self])]
                                     /\ IF msg_c[self].callType = WRITE_RESP
                                           THEN /\ allSubmittedWriteOps' = [allSubmittedWriteOps EXCEPT ![msg_c[self].op.obj] = allSubmittedWriteOps[msg_c[self].op.obj] \cup {msg_c[self]}]
                                                /\ UNCHANGED allSubmittedReadOps
                                           ELSE /\ allSubmittedReadOps' = [allSubmittedReadOps EXCEPT ![msg_c[self].op.obj] = allSubmittedReadOps[msg_c[self].op.obj] \cup {msg_c[self]}]
                                                /\ UNCHANGED allSubmittedWriteOps
                                     /\ Assert((msg_c[self].uniqueId[1] = self), 
                                               "Failure of assertion at line 393, column 17.")
                                     /\ msg_c' = [msg_c EXCEPT ![self] = NullReq]
                                     /\ pc' = [pc EXCEPT ![self] = "readOrWrite"]
                                     /\ UNCHANGED << msgQs, outstandingOps >>
                          /\ UNCHANGED << failoverMsgQs, objLogs, 
                                          terminatedYet, nonInitClients, start, 
                                          timeOracle, Successors, Predecessors, 
                                          currentHead, currentTail, 
                                          uninitializedObjs, initObj, 
                                          objs_init, obj_init, actions_init, 
                                          action_init, gateway_cinit, 
                                          msg_cinit, uniqueId_cinit, 
                                          sentOps_init, recvdOps_init, 
                                          crashNode, objs, obj, actions, 
                                          action, gateway_c, crashedNode, 
                                          sender_zk, liveNode, req_z, 
                                          liveNodes, role, sender, req, 
                                          pendingInvos, failoverPendingInvos, 
                                          now, failoverUnpropagatedWrites, 
                                          failoverAckdWrites, version, 
                                          pendingInvo >>

waitForOps(self) == /\ pc[self] = "waitForOps"
                    /\ IF outstandingOps[self] > 0
                          THEN /\ \E temp \in {s \in SendersTo(self): msgQs[<<s, self>>] /= << >>}:
                                    /\ gateway_c' = [gateway_c EXCEPT ![self] = temp]
                                    /\ outstandingOps' = [outstandingOps EXCEPT ![self] = outstandingOps[self] - 1]
                               /\ pc' = [pc EXCEPT ![self] = "waitForOps"]
                               /\ UNCHANGED << msgQs, msg_c >>
                          ELSE /\ msgQs[<<gateway_c[self], self>>] /= << >>
                               /\ msg_c' = [msg_c EXCEPT ![self] = Head(msgQs[<<gateway_c[self], self>>])]
                               /\ msgQs' = [msgQs EXCEPT ![<<gateway_c[self], self>>] = Tail(@)]
                               /\ pc' = [pc EXCEPT ![self] = "sendToActiveNode"]
                               /\ UNCHANGED << gateway_c, outstandingOps >>
                    /\ UNCHANGED << failoverMsgQs, objLogs, 
                                    allSubmittedWriteOps, allSubmittedReadOps, 
                                    terminatedYet, nonInitClients, start, 
                                    timeOracle, Successors, Predecessors, 
                                    currentHead, currentTail, 
                                    uninitializedObjs, initObj, objs_init, 
                                    obj_init, actions_init, action_init, 
                                    gateway_cinit, msg_cinit, uniqueId_cinit, 
                                    sentOps_init, recvdOps_init, crashNode, 
                                    objs, obj, actions, action, uniqueId, 
                                    crashedNode, sender_zk, liveNode, req_z, 
                                    liveNodes, role, sender, req, pendingInvos, 
                                    failoverPendingInvos, now, 
                                    failoverUnpropagatedWrites, 
                                    failoverAckdWrites, version, pendingInvo >>

terminate(self) == /\ pc[self] = "terminate"
                   /\ terminatedYet' = [terminatedYet EXCEPT ![self] = TRUE]
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << msgQs, failoverMsgQs, objLogs, 
                                   allSubmittedWriteOps, allSubmittedReadOps, 
                                   nonInitClients, start, timeOracle, 
                                   Successors, Predecessors, currentHead, 
                                   currentTail, uninitializedObjs, initObj, 
                                   objs_init, obj_init, actions_init, 
                                   action_init, gateway_cinit, msg_cinit, 
                                   uniqueId_cinit, sentOps_init, recvdOps_init, 
                                   crashNode, objs, obj, actions, action, 
                                   gateway_c, msg_c, uniqueId, outstandingOps, 
                                   crashedNode, sender_zk, liveNode, req_z, 
                                   liveNodes, role, sender, req, pendingInvos, 
                                   failoverPendingInvos, now, 
                                   failoverUnpropagatedWrites, 
                                   failoverAckdWrites, version, pendingInvo >>

c(self) == waitForInit(self) \/ concurrentOps(self) \/ readOrWrite(self)
              \/ sendToActiveNode(self) \/ waitForOps(self)
              \/ terminate(self)

listen_z == /\ pc["zookeeper"] = "listen_z"
            /\ \E temp \in {s \in SendersTo(Zookeeper): msgQs[<<s, Zookeeper>>] /= << >>}:
                 sender_zk' = temp
            /\ msgQs[<<sender_zk', Zookeeper>>] /= << >>
            /\ req_z' = Head(msgQs[<<sender_zk', Zookeeper>>])
            /\ msgQs' = [msgQs EXCEPT ![<<sender_zk', Zookeeper>>] = Tail(@)]
            /\ IF req_z'.callType = ZK_SESSION_ENDED
                  THEN /\ crashedNode' = sender_zk'
                       /\ liveNodes' = Nodes \ {crashedNode'}
                       /\ pc' = [pc EXCEPT !["zookeeper"] = "triggerWatchesNodeDel"]
                  ELSE /\ IF req_z'.callType = ZK_CREATE
                             THEN /\ liveNodes' = Nodes
                                  /\ pc' = [pc EXCEPT !["zookeeper"] = "triggerWatchesNodeAdd"]
                             ELSE /\ pc' = [pc EXCEPT !["zookeeper"] = "listen_z"]
                                  /\ UNCHANGED liveNodes
                       /\ UNCHANGED crashedNode
            /\ UNCHANGED << failoverMsgQs, objLogs, allSubmittedWriteOps, 
                            allSubmittedReadOps, terminatedYet, nonInitClients, 
                            start, timeOracle, Successors, Predecessors, 
                            currentHead, currentTail, uninitializedObjs, 
                            initObj, objs_init, obj_init, actions_init, 
                            action_init, gateway_cinit, msg_cinit, 
                            uniqueId_cinit, sentOps_init, recvdOps_init, 
                            crashNode, objs, obj, actions, action, gateway_c, 
                            msg_c, uniqueId, outstandingOps, liveNode, role, 
                            sender, req, pendingInvos, failoverPendingInvos, 
                            now, failoverUnpropagatedWrites, 
                            failoverAckdWrites, version, pendingInvo >>

triggerWatchesNodeDel == /\ pc["zookeeper"] = "triggerWatchesNodeDel"
                         /\ IF liveNodes /= {}
                               THEN /\ liveNode' = (CHOOSE ln \in liveNodes: TRUE)
                                    /\ msgQs' = [msgQs EXCEPT ![<<Zookeeper, liveNode'>>] = Append(@, ([ callType    |-> ZK_NODE_DEL,
                                                                                                         crashedNode  |-> crashedNode]))]
                                    /\ liveNodes' = liveNodes \ {liveNode'}
                                    /\ pc' = [pc EXCEPT !["zookeeper"] = "triggerWatchesNodeDel"]
                               ELSE /\ pc' = [pc EXCEPT !["zookeeper"] = "listen_z"]
                                    /\ UNCHANGED << msgQs, liveNode, liveNodes >>
                         /\ UNCHANGED << failoverMsgQs, objLogs, 
                                         allSubmittedWriteOps, 
                                         allSubmittedReadOps, terminatedYet, 
                                         nonInitClients, start, timeOracle, 
                                         Successors, Predecessors, currentHead, 
                                         currentTail, uninitializedObjs, 
                                         initObj, objs_init, obj_init, 
                                         actions_init, action_init, 
                                         gateway_cinit, msg_cinit, 
                                         uniqueId_cinit, sentOps_init, 
                                         recvdOps_init, crashNode, objs, obj, 
                                         actions, action, gateway_c, msg_c, 
                                         uniqueId, outstandingOps, crashedNode, 
                                         sender_zk, req_z, role, sender, req, 
                                         pendingInvos, failoverPendingInvos, 
                                         now, failoverUnpropagatedWrites, 
                                         failoverAckdWrites, version, 
                                         pendingInvo >>

triggerWatchesNodeAdd == /\ pc["zookeeper"] = "triggerWatchesNodeAdd"
                         /\ IF liveNodes /= {}
                               THEN /\ liveNode' = (CHOOSE ln \in liveNodes : TRUE)
                                    /\ failoverMsgQs' = [failoverMsgQs EXCEPT ![<<Zookeeper, liveNode'>>] = Append(@, ([ callType |-> ZK_NODE_ADD]))]
                                    /\ liveNodes' = liveNodes \ {liveNode'}
                                    /\ pc' = [pc EXCEPT !["zookeeper"] = "triggerWatchesNodeAdd"]
                               ELSE /\ liveNodes' = Clients
                                    /\ pc' = [pc EXCEPT !["zookeeper"] = "timeoutClients"]
                                    /\ UNCHANGED << failoverMsgQs, liveNode >>
                         /\ UNCHANGED << msgQs, objLogs, allSubmittedWriteOps, 
                                         allSubmittedReadOps, terminatedYet, 
                                         nonInitClients, start, timeOracle, 
                                         Successors, Predecessors, currentHead, 
                                         currentTail, uninitializedObjs, 
                                         initObj, objs_init, obj_init, 
                                         actions_init, action_init, 
                                         gateway_cinit, msg_cinit, 
                                         uniqueId_cinit, sentOps_init, 
                                         recvdOps_init, crashNode, objs, obj, 
                                         actions, action, gateway_c, msg_c, 
                                         uniqueId, outstandingOps, crashedNode, 
                                         sender_zk, req_z, role, sender, req, 
                                         pendingInvos, failoverPendingInvos, 
                                         now, failoverUnpropagatedWrites, 
                                         failoverAckdWrites, version, 
                                         pendingInvo >>

timeoutClients == /\ pc["zookeeper"] = "timeoutClients"
                  /\ IF liveNodes /= {}
                        THEN /\ liveNode' = (CHOOSE client \in liveNodes : TRUE)
                             /\ liveNodes' = liveNodes \ {liveNode'}
                             /\ IF msgQs[<<liveNode', crashedNode>>] /= << >>
                                   THEN /\ msgQs' = [msgQs EXCEPT ![<<Zookeeper, liveNode'>>] = Append(@, ([callType |-> TIMEOUT]))]
                                   ELSE /\ TRUE
                                        /\ msgQs' = msgQs
                             /\ pc' = [pc EXCEPT !["zookeeper"] = "timeoutClients"]
                        ELSE /\ pc' = [pc EXCEPT !["zookeeper"] = "listen_z"]
                             /\ UNCHANGED << msgQs, liveNode, liveNodes >>
                  /\ UNCHANGED << failoverMsgQs, objLogs, allSubmittedWriteOps, 
                                  allSubmittedReadOps, terminatedYet, 
                                  nonInitClients, start, timeOracle, 
                                  Successors, Predecessors, currentHead, 
                                  currentTail, uninitializedObjs, initObj, 
                                  objs_init, obj_init, actions_init, 
                                  action_init, gateway_cinit, msg_cinit, 
                                  uniqueId_cinit, sentOps_init, recvdOps_init, 
                                  crashNode, objs, obj, actions, action, 
                                  gateway_c, msg_c, uniqueId, outstandingOps, 
                                  crashedNode, sender_zk, req_z, role, sender, 
                                  req, pendingInvos, failoverPendingInvos, now, 
                                  failoverUnpropagatedWrites, 
                                  failoverAckdWrites, version, pendingInvo >>

zk == listen_z \/ triggerWatchesNodeDel \/ triggerWatchesNodeAdd
         \/ timeoutClients

roleAssignment(self) == /\ pc[self] = "roleAssignment"
                        /\ role' = [role EXCEPT ![self] = CASE self = head -> HEAD
                                                          [] self = tail -> TAIL
                                                          [] OTHER -> MID]
                        /\ pc' = [pc EXCEPT ![self] = "listen"]
                        /\ UNCHANGED << msgQs, failoverMsgQs, objLogs, 
                                        allSubmittedWriteOps, 
                                        allSubmittedReadOps, terminatedYet, 
                                        nonInitClients, start, timeOracle, 
                                        Successors, Predecessors, currentHead, 
                                        currentTail, uninitializedObjs, 
                                        initObj, objs_init, obj_init, 
                                        actions_init, action_init, 
                                        gateway_cinit, msg_cinit, 
                                        uniqueId_cinit, sentOps_init, 
                                        recvdOps_init, crashNode, objs, obj, 
                                        actions, action, gateway_c, msg_c, 
                                        uniqueId, outstandingOps, crashedNode, 
                                        sender_zk, liveNode, req_z, liveNodes, 
                                        sender, req, pendingInvos, 
                                        failoverPendingInvos, now, 
                                        failoverUnpropagatedWrites, 
                                        failoverAckdWrites, version, 
                                        pendingInvo >>

listen(self) == /\ pc[self] = "listen"
                /\ \E temp \in {s \in SendersTo(self): msgQs[<<s, self>>] /= << >>}:
                     sender' = [sender EXCEPT ![self] = temp]
                /\ msgQs[<<sender'[self], self>>] /= << >>
                /\ req' = [req EXCEPT ![self] = Head(msgQs[<<sender'[self], self>>])]
                /\ msgQs' = [msgQs EXCEPT ![<<sender'[self], self>>] = Tail(@)]
                /\ IF role[self] = HEAD
                      THEN /\ IF req'[self].callType = READ_INV
                                 THEN /\ pc' = [pc EXCEPT ![self] = "handleReadInv"]
                                 ELSE /\ IF req'[self].callType = READ_RESP
                                            THEN /\ pc' = [pc EXCEPT ![self] = "handleReadResp"]
                                            ELSE /\ IF req'[self].callType = WRITE_INV
                                                       THEN /\ pc' = [pc EXCEPT ![self] = "handleWriteInvHead"]
                                                       ELSE /\ IF req'[self].callType = WRITE_RESP
                                                                  THEN /\ pc' = [pc EXCEPT ![self] = "handleWriteResp"]
                                                                  ELSE /\ IF req'[self].callType = CRASH
                                                                             THEN /\ pc' = [pc EXCEPT ![self] = "crash"]
                                                                             ELSE /\ IF req'[self].callType = ZK_NODE_DEL
                                                                                        THEN /\ IF req'[self].crashedNode = Successors[self]
                                                                                                   THEN /\ pc' = [pc EXCEPT ![self] = "failoverCrashedNodeIsSuccessor"]
                                                                                                   ELSE /\ IF req'[self].crashedNode = Predecessors[self]
                                                                                                              THEN /\ pc' = [pc EXCEPT ![self] = "failoverCrashedNodeIsPredecessor"]
                                                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "failoverListen"]
                                                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "listen"]
                      ELSE /\ IF role[self] = TAIL
                                 THEN /\ IF req'[self].callType = READ_INV
                                            THEN /\ pc' = [pc EXCEPT ![self] = "handleReadInvTail"]
                                            ELSE /\ IF req'[self].callType = WRITE_INV
                                                       THEN /\ pc' = [pc EXCEPT ![self] = "handleWriteInvTail"]
                                                       ELSE /\ IF req'[self].callType = CRASH
                                                                  THEN /\ pc' = [pc EXCEPT ![self] = "crash"]
                                                                  ELSE /\ IF req'[self].callType = ZK_NODE_DEL
                                                                             THEN /\ IF Predecessors[self] = req'[self].crashedNode
                                                                                        THEN /\ pc' = [pc EXCEPT ![self] = "failoverCrashedNodeIsPredecessor"]
                                                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "failoverListen"]
                                                                             ELSE /\ pc' = [pc EXCEPT ![self] = "listen"]
                                 ELSE /\ IF req'[self].callType = READ_INV
                                            THEN /\ pc' = [pc EXCEPT ![self] = "handleReadInv"]
                                            ELSE /\ IF req'[self].callType = READ_RESP
                                                       THEN /\ pc' = [pc EXCEPT ![self] = "handleReadResp"]
                                                       ELSE /\ IF req'[self].callType = WRITE_INV
                                                                  THEN /\ pc' = [pc EXCEPT ![self] = "handleWriteInv"]
                                                                  ELSE /\ IF req'[self].callType = WRITE_RESP
                                                                             THEN /\ pc' = [pc EXCEPT ![self] = "handleWriteResp"]
                                                                             ELSE /\ IF req'[self].callType = CRASH
                                                                                        THEN /\ pc' = [pc EXCEPT ![self] = "crash"]
                                                                                        ELSE /\ IF req'[self].callType = ZK_NODE_DEL
                                                                                                   THEN /\ IF req'[self].crashedNode = Successors[self]
                                                                                                              THEN /\ pc' = [pc EXCEPT ![self] = "failoverCrashedNodeIsSuccessor"]
                                                                                                              ELSE /\ IF req'[self].crashedNode = Predecessors[self]
                                                                                                                         THEN /\ pc' = [pc EXCEPT ![self] = "failoverCrashedNodeIsPredecessor"]
                                                                                                                         ELSE /\ pc' = [pc EXCEPT ![self] = "failoverListen"]
                                                                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "listen"]
                /\ UNCHANGED << failoverMsgQs, objLogs, allSubmittedWriteOps, 
                                allSubmittedReadOps, terminatedYet, 
                                nonInitClients, start, timeOracle, Successors, 
                                Predecessors, currentHead, currentTail, 
                                uninitializedObjs, initObj, objs_init, 
                                obj_init, actions_init, action_init, 
                                gateway_cinit, msg_cinit, uniqueId_cinit, 
                                sentOps_init, recvdOps_init, crashNode, objs, 
                                obj, actions, action, gateway_c, msg_c, 
                                uniqueId, outstandingOps, crashedNode, 
                                sender_zk, liveNode, req_z, liveNodes, role, 
                                pendingInvos, failoverPendingInvos, now, 
                                failoverUnpropagatedWrites, failoverAckdWrites, 
                                version, pendingInvo >>

failoverListen(self) == /\ pc[self] = "failoverListen"
                        /\ \E temp \in {s \in SendersTo(self): failoverMsgQs[<<s, self>>] /= << >>}:
                             sender' = [sender EXCEPT ![self] = temp]
                        /\ failoverMsgQs[<<sender'[self], self>>] /= << >>
                        /\ req' = [req EXCEPT ![self] = Head(failoverMsgQs[<<sender'[self], self>>])]
                        /\ failoverMsgQs' = [failoverMsgQs EXCEPT ![<<sender'[self], self>>] = Tail(@)]
                        /\ IF req'[self].callType = FAILOVER_NOTIFY_TAIL
                              THEN /\ IF role[self] = TAIL
                                         THEN /\ pc' = [pc EXCEPT ![self] = "failoverTailPropsLog"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "failoverListen"]
                              ELSE /\ IF req'[self].callType = FAILOVER_PROPAGATE_LOG
                                         THEN /\ pc' = [pc EXCEPT ![self] = "failoverAssumeNewTail"]
                                         ELSE /\ IF req'[self].callType = ZK_NODE_ADD
                                                    THEN /\ pc' = [pc EXCEPT ![self] = "listen"]
                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "failoverListen"]
                        /\ UNCHANGED << msgQs, objLogs, allSubmittedWriteOps, 
                                        allSubmittedReadOps, terminatedYet, 
                                        nonInitClients, start, timeOracle, 
                                        Successors, Predecessors, currentHead, 
                                        currentTail, uninitializedObjs, 
                                        initObj, objs_init, obj_init, 
                                        actions_init, action_init, 
                                        gateway_cinit, msg_cinit, 
                                        uniqueId_cinit, sentOps_init, 
                                        recvdOps_init, crashNode, objs, obj, 
                                        actions, action, gateway_c, msg_c, 
                                        uniqueId, outstandingOps, crashedNode, 
                                        sender_zk, liveNode, req_z, liveNodes, 
                                        role, pendingInvos, 
                                        failoverPendingInvos, now, 
                                        failoverUnpropagatedWrites, 
                                        failoverAckdWrites, version, 
                                        pendingInvo >>

handleReadInv(self) == /\ pc[self] = "handleReadInv"
                       /\ IF IsDirty(self, req[self].op.obj)
                             THEN /\ pc' = [pc EXCEPT ![self] = "apportionQ"]
                                  /\ UNCHANGED << msgQs, timeOracle, req, now >>
                             ELSE /\ now' = [now EXCEPT ![self] = timeOracle]
                                  /\ timeOracle' = timeOracle + 1
                                  /\ req' = [req EXCEPT ![self] = [    callType    |-> READ_RESP,
                                                                       uniqueId    |-> req[self].uniqueId,
                                                                       startTs     |-> now'[self],
                                                                       commitTs    |-> now'[self],
                                                                       op          |-> Read(self, req[self].op.obj)]]
                                  /\ msgQs' = [msgQs EXCEPT ![<<self, sender[self]>>] = Append(@, req'[self])]
                                  /\ pc' = [pc EXCEPT ![self] = "finishReadInv"]
                       /\ UNCHANGED << failoverMsgQs, objLogs, 
                                       allSubmittedWriteOps, 
                                       allSubmittedReadOps, terminatedYet, 
                                       nonInitClients, start, Successors, 
                                       Predecessors, currentHead, currentTail, 
                                       uninitializedObjs, initObj, objs_init, 
                                       obj_init, actions_init, action_init, 
                                       gateway_cinit, msg_cinit, 
                                       uniqueId_cinit, sentOps_init, 
                                       recvdOps_init, crashNode, objs, obj, 
                                       actions, action, gateway_c, msg_c, 
                                       uniqueId, outstandingOps, crashedNode, 
                                       sender_zk, liveNode, req_z, liveNodes, 
                                       role, sender, pendingInvos, 
                                       failoverPendingInvos, 
                                       failoverUnpropagatedWrites, 
                                       failoverAckdWrites, version, 
                                       pendingInvo >>

apportionQ(self) == /\ pc[self] = "apportionQ"
                    /\ msgQs' = [msgQs EXCEPT ![<<self, currentTail>>] = Append(@, req[self])]
                    /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \cup {<<(req[self].uniqueId), sender[self]>>}]
                    /\ pc' = [pc EXCEPT ![self] = "finishReadInv"]
                    /\ UNCHANGED << failoverMsgQs, objLogs, 
                                    allSubmittedWriteOps, allSubmittedReadOps, 
                                    terminatedYet, nonInitClients, start, 
                                    timeOracle, Successors, Predecessors, 
                                    currentHead, currentTail, 
                                    uninitializedObjs, initObj, objs_init, 
                                    obj_init, actions_init, action_init, 
                                    gateway_cinit, msg_cinit, uniqueId_cinit, 
                                    sentOps_init, recvdOps_init, crashNode, 
                                    objs, obj, actions, action, gateway_c, 
                                    msg_c, uniqueId, outstandingOps, 
                                    crashedNode, sender_zk, liveNode, req_z, 
                                    liveNodes, role, sender, req, 
                                    failoverPendingInvos, now, 
                                    failoverUnpropagatedWrites, 
                                    failoverAckdWrites, version, pendingInvo >>

finishReadInv(self) == /\ pc[self] = "finishReadInv"
                       /\ pc' = [pc EXCEPT ![self] = "listen"]
                       /\ UNCHANGED << msgQs, failoverMsgQs, objLogs, 
                                       allSubmittedWriteOps, 
                                       allSubmittedReadOps, terminatedYet, 
                                       nonInitClients, start, timeOracle, 
                                       Successors, Predecessors, currentHead, 
                                       currentTail, uninitializedObjs, initObj, 
                                       objs_init, obj_init, actions_init, 
                                       action_init, gateway_cinit, msg_cinit, 
                                       uniqueId_cinit, sentOps_init, 
                                       recvdOps_init, crashNode, objs, obj, 
                                       actions, action, gateway_c, msg_c, 
                                       uniqueId, outstandingOps, crashedNode, 
                                       sender_zk, liveNode, req_z, liveNodes, 
                                       role, sender, req, pendingInvos, 
                                       failoverPendingInvos, now, 
                                       failoverUnpropagatedWrites, 
                                       failoverAckdWrites, version, 
                                       pendingInvo >>

handleReadInvTail(self) == /\ pc[self] = "handleReadInvTail"
                           /\ now' = [now EXCEPT ![self] = timeOracle]
                           /\ timeOracle' = timeOracle + 1
                           /\ req' = [req EXCEPT ![self] = [ callType |-> READ_RESP,
                                                             uniqueId |-> req[self].uniqueId,
                                                             startTs |-> now'[self],
                                                             commitTs |-> now'[self],
                                                             op |-> Read(self, req[self].op.obj)]]
                           /\ msgQs' = [msgQs EXCEPT ![<<self, sender[self]>>] = Append(@, req'[self])]
                           /\ pc' = [pc EXCEPT ![self] = "finishReadInvTail"]
                           /\ UNCHANGED << failoverMsgQs, objLogs, 
                                           allSubmittedWriteOps, 
                                           allSubmittedReadOps, terminatedYet, 
                                           nonInitClients, start, Successors, 
                                           Predecessors, currentHead, 
                                           currentTail, uninitializedObjs, 
                                           initObj, objs_init, obj_init, 
                                           actions_init, action_init, 
                                           gateway_cinit, msg_cinit, 
                                           uniqueId_cinit, sentOps_init, 
                                           recvdOps_init, crashNode, objs, obj, 
                                           actions, action, gateway_c, msg_c, 
                                           uniqueId, outstandingOps, 
                                           crashedNode, sender_zk, liveNode, 
                                           req_z, liveNodes, role, sender, 
                                           pendingInvos, failoverPendingInvos, 
                                           failoverUnpropagatedWrites, 
                                           failoverAckdWrites, version, 
                                           pendingInvo >>

finishReadInvTail(self) == /\ pc[self] = "finishReadInvTail"
                           /\ pc' = [pc EXCEPT ![self] = "listen"]
                           /\ UNCHANGED << msgQs, failoverMsgQs, objLogs, 
                                           allSubmittedWriteOps, 
                                           allSubmittedReadOps, terminatedYet, 
                                           nonInitClients, start, timeOracle, 
                                           Successors, Predecessors, 
                                           currentHead, currentTail, 
                                           uninitializedObjs, initObj, 
                                           objs_init, obj_init, actions_init, 
                                           action_init, gateway_cinit, 
                                           msg_cinit, uniqueId_cinit, 
                                           sentOps_init, recvdOps_init, 
                                           crashNode, objs, obj, actions, 
                                           action, gateway_c, msg_c, uniqueId, 
                                           outstandingOps, crashedNode, 
                                           sender_zk, liveNode, req_z, 
                                           liveNodes, role, sender, req, 
                                           pendingInvos, failoverPendingInvos, 
                                           now, failoverUnpropagatedWrites, 
                                           failoverAckdWrites, version, 
                                           pendingInvo >>

handleReadResp(self) == /\ pc[self] = "handleReadResp"
                        /\ msgQs' = [msgQs EXCEPT ![<<self, (Find(pendingInvos[self], req[self].uniqueId))>>] = Append(@, req[self])]
                        /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \ {FindPair(pendingInvos[self], (req[self].uniqueId))}]
                        /\ pc' = [pc EXCEPT ![self] = "finishReadResp"]
                        /\ UNCHANGED << failoverMsgQs, objLogs, 
                                        allSubmittedWriteOps, 
                                        allSubmittedReadOps, terminatedYet, 
                                        nonInitClients, start, timeOracle, 
                                        Successors, Predecessors, currentHead, 
                                        currentTail, uninitializedObjs, 
                                        initObj, objs_init, obj_init, 
                                        actions_init, action_init, 
                                        gateway_cinit, msg_cinit, 
                                        uniqueId_cinit, sentOps_init, 
                                        recvdOps_init, crashNode, objs, obj, 
                                        actions, action, gateway_c, msg_c, 
                                        uniqueId, outstandingOps, crashedNode, 
                                        sender_zk, liveNode, req_z, liveNodes, 
                                        role, sender, req, 
                                        failoverPendingInvos, now, 
                                        failoverUnpropagatedWrites, 
                                        failoverAckdWrites, version, 
                                        pendingInvo >>

finishReadResp(self) == /\ pc[self] = "finishReadResp"
                        /\ pc' = [pc EXCEPT ![self] = "listen"]
                        /\ UNCHANGED << msgQs, failoverMsgQs, objLogs, 
                                        allSubmittedWriteOps, 
                                        allSubmittedReadOps, terminatedYet, 
                                        nonInitClients, start, timeOracle, 
                                        Successors, Predecessors, currentHead, 
                                        currentTail, uninitializedObjs, 
                                        initObj, objs_init, obj_init, 
                                        actions_init, action_init, 
                                        gateway_cinit, msg_cinit, 
                                        uniqueId_cinit, sentOps_init, 
                                        recvdOps_init, crashNode, objs, obj, 
                                        actions, action, gateway_c, msg_c, 
                                        uniqueId, outstandingOps, crashedNode, 
                                        sender_zk, liveNode, req_z, liveNodes, 
                                        role, sender, req, pendingInvos, 
                                        failoverPendingInvos, now, 
                                        failoverUnpropagatedWrites, 
                                        failoverAckdWrites, version, 
                                        pendingInvo >>

handleWriteInvHead(self) == /\ pc[self] = "handleWriteInvHead"
                            /\ now' = [now EXCEPT ![self] = timeOracle]
                            /\ timeOracle' = timeOracle + 1
                            /\ req' = [req EXCEPT ![self] = [req[self] EXCEPT  !.startTs = now'[self],
                                                                               !.op.writeStartTs = now'[self],
                                                                               !.op.commitStatus = DIRTY]]
                            /\ objLogs' = [objLogs EXCEPT ![self][(req'[self].op).obj] = Cons((req'[self].op), @)]
                            /\ msgQs' = [msgQs EXCEPT ![<<self, (Successors[self])>>] = Append(@, req'[self])]
                            /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \cup {<<(req'[self].uniqueId), sender[self]>>}]
                            /\ pc' = [pc EXCEPT ![self] = "finishWriteInvHead"]
                            /\ UNCHANGED << failoverMsgQs, 
                                            allSubmittedWriteOps, 
                                            allSubmittedReadOps, terminatedYet, 
                                            nonInitClients, start, Successors, 
                                            Predecessors, currentHead, 
                                            currentTail, uninitializedObjs, 
                                            initObj, objs_init, obj_init, 
                                            actions_init, action_init, 
                                            gateway_cinit, msg_cinit, 
                                            uniqueId_cinit, sentOps_init, 
                                            recvdOps_init, crashNode, objs, 
                                            obj, actions, action, gateway_c, 
                                            msg_c, uniqueId, outstandingOps, 
                                            crashedNode, sender_zk, liveNode, 
                                            req_z, liveNodes, role, sender, 
                                            failoverPendingInvos, 
                                            failoverUnpropagatedWrites, 
                                            failoverAckdWrites, version, 
                                            pendingInvo >>

finishWriteInvHead(self) == /\ pc[self] = "finishWriteInvHead"
                            /\ pc' = [pc EXCEPT ![self] = "listen"]
                            /\ UNCHANGED << msgQs, failoverMsgQs, objLogs, 
                                            allSubmittedWriteOps, 
                                            allSubmittedReadOps, terminatedYet, 
                                            nonInitClients, start, timeOracle, 
                                            Successors, Predecessors, 
                                            currentHead, currentTail, 
                                            uninitializedObjs, initObj, 
                                            objs_init, obj_init, actions_init, 
                                            action_init, gateway_cinit, 
                                            msg_cinit, uniqueId_cinit, 
                                            sentOps_init, recvdOps_init, 
                                            crashNode, objs, obj, actions, 
                                            action, gateway_c, msg_c, uniqueId, 
                                            outstandingOps, crashedNode, 
                                            sender_zk, liveNode, req_z, 
                                            liveNodes, role, sender, req, 
                                            pendingInvos, failoverPendingInvos, 
                                            now, failoverUnpropagatedWrites, 
                                            failoverAckdWrites, version, 
                                            pendingInvo >>

handleWriteInv(self) == /\ pc[self] = "handleWriteInv"
                        /\ objLogs' = [objLogs EXCEPT ![self][(req[self].op).obj] = Cons((req[self].op), @)]
                        /\ msgQs' = [msgQs EXCEPT ![<<self, (Successors[self])>>] = Append(@, req[self])]
                        /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \cup {<<(req[self].uniqueId), sender[self]>>}]
                        /\ pc' = [pc EXCEPT ![self] = "finishWriteInv"]
                        /\ UNCHANGED << failoverMsgQs, allSubmittedWriteOps, 
                                        allSubmittedReadOps, terminatedYet, 
                                        nonInitClients, start, timeOracle, 
                                        Successors, Predecessors, currentHead, 
                                        currentTail, uninitializedObjs, 
                                        initObj, objs_init, obj_init, 
                                        actions_init, action_init, 
                                        gateway_cinit, msg_cinit, 
                                        uniqueId_cinit, sentOps_init, 
                                        recvdOps_init, crashNode, objs, obj, 
                                        actions, action, gateway_c, msg_c, 
                                        uniqueId, outstandingOps, crashedNode, 
                                        sender_zk, liveNode, req_z, liveNodes, 
                                        role, sender, req, 
                                        failoverPendingInvos, now, 
                                        failoverUnpropagatedWrites, 
                                        failoverAckdWrites, version, 
                                        pendingInvo >>

finishWriteInv(self) == /\ pc[self] = "finishWriteInv"
                        /\ pc' = [pc EXCEPT ![self] = "listen"]
                        /\ UNCHANGED << msgQs, failoverMsgQs, objLogs, 
                                        allSubmittedWriteOps, 
                                        allSubmittedReadOps, terminatedYet, 
                                        nonInitClients, start, timeOracle, 
                                        Successors, Predecessors, currentHead, 
                                        currentTail, uninitializedObjs, 
                                        initObj, objs_init, obj_init, 
                                        actions_init, action_init, 
                                        gateway_cinit, msg_cinit, 
                                        uniqueId_cinit, sentOps_init, 
                                        recvdOps_init, crashNode, objs, obj, 
                                        actions, action, gateway_c, msg_c, 
                                        uniqueId, outstandingOps, crashedNode, 
                                        sender_zk, liveNode, req_z, liveNodes, 
                                        role, sender, req, pendingInvos, 
                                        failoverPendingInvos, now, 
                                        failoverUnpropagatedWrites, 
                                        failoverAckdWrites, version, 
                                        pendingInvo >>

handleWriteInvTail(self) == /\ pc[self] = "handleWriteInvTail"
                            /\ now' = [now EXCEPT ![self] = timeOracle]
                            /\ timeOracle' = timeOracle + 1
                            /\ objLogs' = [objLogs EXCEPT ![self][([req[self].op EXCEPT  !.writeCommitTs = now'[self],
                                                                                         !.commitStatus = CLEAN]).obj] = Cons(([req[self].op EXCEPT  !.writeCommitTs = now'[self],
                                                                                                                                                     !.commitStatus = CLEAN]), @)]
                            /\ pc' = [pc EXCEPT ![self] = "tailAck"]
                            /\ UNCHANGED << msgQs, failoverMsgQs, 
                                            allSubmittedWriteOps, 
                                            allSubmittedReadOps, terminatedYet, 
                                            nonInitClients, start, Successors, 
                                            Predecessors, currentHead, 
                                            currentTail, uninitializedObjs, 
                                            initObj, objs_init, obj_init, 
                                            actions_init, action_init, 
                                            gateway_cinit, msg_cinit, 
                                            uniqueId_cinit, sentOps_init, 
                                            recvdOps_init, crashNode, objs, 
                                            obj, actions, action, gateway_c, 
                                            msg_c, uniqueId, outstandingOps, 
                                            crashedNode, sender_zk, liveNode, 
                                            req_z, liveNodes, role, sender, 
                                            req, pendingInvos, 
                                            failoverPendingInvos, 
                                            failoverUnpropagatedWrites, 
                                            failoverAckdWrites, version, 
                                            pendingInvo >>

tailAck(self) == /\ pc[self] = "tailAck"
                 /\ req' = [req EXCEPT ![self] = [   callType |-> WRITE_RESP,
                                                     uniqueId |-> req[self].uniqueId,
                                                     startTs  |-> req[self].startTs,
                                                     commitTs |-> Read(self, req[self].op.obj).writeCommitTs,
                                                     op |-> Read(self, req[self].op.obj)]]
                 /\ msgQs' = [msgQs EXCEPT ![<<self, (Predecessors[self])>>] = Append(@, req'[self])]
                 /\ pc' = [pc EXCEPT ![self] = "finishWriteInvTail"]
                 /\ UNCHANGED << failoverMsgQs, objLogs, allSubmittedWriteOps, 
                                 allSubmittedReadOps, terminatedYet, 
                                 nonInitClients, start, timeOracle, Successors, 
                                 Predecessors, currentHead, currentTail, 
                                 uninitializedObjs, initObj, objs_init, 
                                 obj_init, actions_init, action_init, 
                                 gateway_cinit, msg_cinit, uniqueId_cinit, 
                                 sentOps_init, recvdOps_init, crashNode, objs, 
                                 obj, actions, action, gateway_c, msg_c, 
                                 uniqueId, outstandingOps, crashedNode, 
                                 sender_zk, liveNode, req_z, liveNodes, role, 
                                 sender, pendingInvos, failoverPendingInvos, 
                                 now, failoverUnpropagatedWrites, 
                                 failoverAckdWrites, version, pendingInvo >>

finishWriteInvTail(self) == /\ pc[self] = "finishWriteInvTail"
                            /\ pc' = [pc EXCEPT ![self] = "listen"]
                            /\ UNCHANGED << msgQs, failoverMsgQs, objLogs, 
                                            allSubmittedWriteOps, 
                                            allSubmittedReadOps, terminatedYet, 
                                            nonInitClients, start, timeOracle, 
                                            Successors, Predecessors, 
                                            currentHead, currentTail, 
                                            uninitializedObjs, initObj, 
                                            objs_init, obj_init, actions_init, 
                                            action_init, gateway_cinit, 
                                            msg_cinit, uniqueId_cinit, 
                                            sentOps_init, recvdOps_init, 
                                            crashNode, objs, obj, actions, 
                                            action, gateway_c, msg_c, uniqueId, 
                                            outstandingOps, crashedNode, 
                                            sender_zk, liveNode, req_z, 
                                            liveNodes, role, sender, req, 
                                            pendingInvos, failoverPendingInvos, 
                                            now, failoverUnpropagatedWrites, 
                                            failoverAckdWrites, version, 
                                            pendingInvo >>

handleWriteResp(self) == /\ pc[self] = "handleWriteResp"
                         /\ objLogs' = [objLogs EXCEPT ![self][req[self].op.obj] = CommitDirtyVersion(@, req[self].op)]
                         /\ msgQs' = [msgQs EXCEPT ![<<self, (Find(pendingInvos[self], req[self].uniqueId))>>] = Append(@, req[self])]
                         /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \ {FindPair(pendingInvos[self], (req[self].uniqueId))}]
                         /\ pc' = [pc EXCEPT ![self] = "finishWriteResp"]
                         /\ UNCHANGED << failoverMsgQs, allSubmittedWriteOps, 
                                         allSubmittedReadOps, terminatedYet, 
                                         nonInitClients, start, timeOracle, 
                                         Successors, Predecessors, currentHead, 
                                         currentTail, uninitializedObjs, 
                                         initObj, objs_init, obj_init, 
                                         actions_init, action_init, 
                                         gateway_cinit, msg_cinit, 
                                         uniqueId_cinit, sentOps_init, 
                                         recvdOps_init, crashNode, objs, obj, 
                                         actions, action, gateway_c, msg_c, 
                                         uniqueId, outstandingOps, crashedNode, 
                                         sender_zk, liveNode, req_z, liveNodes, 
                                         role, sender, req, 
                                         failoverPendingInvos, now, 
                                         failoverUnpropagatedWrites, 
                                         failoverAckdWrites, version, 
                                         pendingInvo >>

finishWriteResp(self) == /\ pc[self] = "finishWriteResp"
                         /\ pc' = [pc EXCEPT ![self] = "listen"]
                         /\ UNCHANGED << msgQs, failoverMsgQs, objLogs, 
                                         allSubmittedWriteOps, 
                                         allSubmittedReadOps, terminatedYet, 
                                         nonInitClients, start, timeOracle, 
                                         Successors, Predecessors, currentHead, 
                                         currentTail, uninitializedObjs, 
                                         initObj, objs_init, obj_init, 
                                         actions_init, action_init, 
                                         gateway_cinit, msg_cinit, 
                                         uniqueId_cinit, sentOps_init, 
                                         recvdOps_init, crashNode, objs, obj, 
                                         actions, action, gateway_c, msg_c, 
                                         uniqueId, outstandingOps, crashedNode, 
                                         sender_zk, liveNode, req_z, liveNodes, 
                                         role, sender, req, pendingInvos, 
                                         failoverPendingInvos, now, 
                                         failoverUnpropagatedWrites, 
                                         failoverAckdWrites, version, 
                                         pendingInvo >>

failoverCrashedNodeIsSuccessor(self) == /\ pc[self] = "failoverCrashedNodeIsSuccessor"
                                        /\ failoverMsgQs' = [failoverMsgQs EXCEPT ![<<self, (Successors[Successors[self]])>>] = Append(@, ([  callType |-> FAILOVER_PROPAGATE_LOG,
                                                                                                                                              log |-> objLogs[self]
                                                                                                                                            ]))]
                                        /\ Successors' = [Successors EXCEPT ![self] = Successors[Successors[self]]]
                                        /\ pc' = [pc EXCEPT ![self] = "finishCrashedNodeIsSuccessor"]
                                        /\ UNCHANGED << msgQs, objLogs, 
                                                        allSubmittedWriteOps, 
                                                        allSubmittedReadOps, 
                                                        terminatedYet, 
                                                        nonInitClients, start, 
                                                        timeOracle, 
                                                        Predecessors, 
                                                        currentHead, 
                                                        currentTail, 
                                                        uninitializedObjs, 
                                                        initObj, objs_init, 
                                                        obj_init, actions_init, 
                                                        action_init, 
                                                        gateway_cinit, 
                                                        msg_cinit, 
                                                        uniqueId_cinit, 
                                                        sentOps_init, 
                                                        recvdOps_init, 
                                                        crashNode, objs, obj, 
                                                        actions, action, 
                                                        gateway_c, msg_c, 
                                                        uniqueId, 
                                                        outstandingOps, 
                                                        crashedNode, sender_zk, 
                                                        liveNode, req_z, 
                                                        liveNodes, role, 
                                                        sender, req, 
                                                        pendingInvos, 
                                                        failoverPendingInvos, 
                                                        now, 
                                                        failoverUnpropagatedWrites, 
                                                        failoverAckdWrites, 
                                                        version, pendingInvo >>

finishCrashedNodeIsSuccessor(self) == /\ pc[self] = "finishCrashedNodeIsSuccessor"
                                      /\ pc' = [pc EXCEPT ![self] = "failoverListen"]
                                      /\ UNCHANGED << msgQs, failoverMsgQs, 
                                                      objLogs, 
                                                      allSubmittedWriteOps, 
                                                      allSubmittedReadOps, 
                                                      terminatedYet, 
                                                      nonInitClients, start, 
                                                      timeOracle, Successors, 
                                                      Predecessors, 
                                                      currentHead, currentTail, 
                                                      uninitializedObjs, 
                                                      initObj, objs_init, 
                                                      obj_init, actions_init, 
                                                      action_init, 
                                                      gateway_cinit, msg_cinit, 
                                                      uniqueId_cinit, 
                                                      sentOps_init, 
                                                      recvdOps_init, crashNode, 
                                                      objs, obj, actions, 
                                                      action, gateway_c, msg_c, 
                                                      uniqueId, outstandingOps, 
                                                      crashedNode, sender_zk, 
                                                      liveNode, req_z, 
                                                      liveNodes, role, sender, 
                                                      req, pendingInvos, 
                                                      failoverPendingInvos, 
                                                      now, 
                                                      failoverUnpropagatedWrites, 
                                                      failoverAckdWrites, 
                                                      version, pendingInvo >>

failoverCrashedNodeIsPredecessor(self) == /\ pc[self] = "failoverCrashedNodeIsPredecessor"
                                          /\ \E temp \in {s \in SendersTo(self): failoverMsgQs[<<s, self>>] /= << >>}:
                                               sender' = [sender EXCEPT ![self] = temp]
                                          /\ failoverMsgQs[<<sender'[self], self>>] /= << >>
                                          /\ req' = [req EXCEPT ![self] = Head(failoverMsgQs[<<sender'[self], self>>])]
                                          /\ failoverMsgQs' = [failoverMsgQs EXCEPT ![<<sender'[self], self>>] = Tail(@)]
                                          /\ Assert((req'[self].callType = FAILOVER_PROPAGATE_LOG), 
                                                    "Failure of assertion at line 717, column 9.")
                                          /\ failoverUnpropagatedWrites' = [failoverUnpropagatedWrites EXCEPT ![self] = FindUnpropagatedWrites(req'[self].log, objLogs[self], Objects)]
                                          /\ pc' = [pc EXCEPT ![self] = "propagateFailedWrites"]
                                          /\ UNCHANGED << msgQs, objLogs, 
                                                          allSubmittedWriteOps, 
                                                          allSubmittedReadOps, 
                                                          terminatedYet, 
                                                          nonInitClients, 
                                                          start, timeOracle, 
                                                          Successors, 
                                                          Predecessors, 
                                                          currentHead, 
                                                          currentTail, 
                                                          uninitializedObjs, 
                                                          initObj, objs_init, 
                                                          obj_init, 
                                                          actions_init, 
                                                          action_init, 
                                                          gateway_cinit, 
                                                          msg_cinit, 
                                                          uniqueId_cinit, 
                                                          sentOps_init, 
                                                          recvdOps_init, 
                                                          crashNode, objs, obj, 
                                                          actions, action, 
                                                          gateway_c, msg_c, 
                                                          uniqueId, 
                                                          outstandingOps, 
                                                          crashedNode, 
                                                          sender_zk, liveNode, 
                                                          req_z, liveNodes, 
                                                          role, pendingInvos, 
                                                          failoverPendingInvos, 
                                                          now, 
                                                          failoverAckdWrites, 
                                                          version, pendingInvo >>

propagateFailedWrites(self) == /\ pc[self] = "propagateFailedWrites"
                               /\ IF failoverUnpropagatedWrites[self] /= {}
                                     THEN /\ version' = [version EXCEPT ![self] = CHOOSE v \in failoverUnpropagatedWrites[self] : TRUE]
                                          /\ objLogs' = [objLogs EXCEPT ![self][version'[self].obj] = Cons(version'[self], @)]
                                          /\ msgQs' = [msgQs EXCEPT ![<<self, (Successors[self])>>] = Append(@, ([  callType |-> WRITE_INV,
                                                                                                                    uniqueId |-> version'[self].uniqueId,
                                                                                                                    startTs |-> version'[self].writeStartTs,
                                                                                                                    commitTs |-> NullTs,
                                                                                                                    op |-> version'[self]]))]
                                          /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \cup {<<(version'[self].uniqueId), sender[self]>>}]
                                          /\ failoverUnpropagatedWrites' = [failoverUnpropagatedWrites EXCEPT ![self] = failoverUnpropagatedWrites[self] \ {version'[self]}]
                                          /\ pc' = [pc EXCEPT ![self] = "propagateFailedWrites"]
                                          /\ UNCHANGED failoverAckdWrites
                                     ELSE /\ failoverAckdWrites' = [failoverAckdWrites EXCEPT ![self] = FindAckdWrites(req[self].log, objLogs[self], Objects)]
                                          /\ pc' = [pc EXCEPT ![self] = "backpropFailedAcks"]
                                          /\ UNCHANGED << msgQs, objLogs, 
                                                          pendingInvos, 
                                                          failoverUnpropagatedWrites, 
                                                          version >>
                               /\ UNCHANGED << failoverMsgQs, 
                                               allSubmittedWriteOps, 
                                               allSubmittedReadOps, 
                                               terminatedYet, nonInitClients, 
                                               start, timeOracle, Successors, 
                                               Predecessors, currentHead, 
                                               currentTail, uninitializedObjs, 
                                               initObj, objs_init, obj_init, 
                                               actions_init, action_init, 
                                               gateway_cinit, msg_cinit, 
                                               uniqueId_cinit, sentOps_init, 
                                               recvdOps_init, crashNode, objs, 
                                               obj, actions, action, gateway_c, 
                                               msg_c, uniqueId, outstandingOps, 
                                               crashedNode, sender_zk, 
                                               liveNode, req_z, liveNodes, 
                                               role, sender, req, 
                                               failoverPendingInvos, now, 
                                               pendingInvo >>

backpropFailedAcks(self) == /\ pc[self] = "backpropFailedAcks"
                            /\ IF failoverAckdWrites[self] /= {}
                                  THEN /\ version' = [version EXCEPT ![self] = CHOOSE v \in failoverAckdWrites[self] : TRUE]
                                       /\ msgQs' = [msgQs EXCEPT ![<<self, (Predecessors[Predecessors[self]])>>] = Append(@, ([  callType |-> WRITE_RESP,
                                                                                                                                 uniqueId |-> version'[self].uniqueId,
                                                                                                                                 startTs |-> version'[self].writeStartTs,
                                                                                                                                 commitTs |-> version'[self].writeCommitTs,
                                                                                                                                 op |-> version'[self]]))]
                                       /\ pc' = [pc EXCEPT ![self] = "backpropFailedAcks"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "notifyTail"]
                                       /\ UNCHANGED << msgQs, version >>
                            /\ UNCHANGED << failoverMsgQs, objLogs, 
                                            allSubmittedWriteOps, 
                                            allSubmittedReadOps, terminatedYet, 
                                            nonInitClients, start, timeOracle, 
                                            Successors, Predecessors, 
                                            currentHead, currentTail, 
                                            uninitializedObjs, initObj, 
                                            objs_init, obj_init, actions_init, 
                                            action_init, gateway_cinit, 
                                            msg_cinit, uniqueId_cinit, 
                                            sentOps_init, recvdOps_init, 
                                            crashNode, objs, obj, actions, 
                                            action, gateway_c, msg_c, uniqueId, 
                                            outstandingOps, crashedNode, 
                                            sender_zk, liveNode, req_z, 
                                            liveNodes, role, sender, req, 
                                            pendingInvos, failoverPendingInvos, 
                                            now, failoverUnpropagatedWrites, 
                                            failoverAckdWrites, pendingInvo >>

notifyTail(self) == /\ pc[self] = "notifyTail"
                    /\ failoverMsgQs' = [failoverMsgQs EXCEPT ![<<self, currentTail>>] = Append(@, ([callType |-> FAILOVER_NOTIFY_TAIL]))]
                    /\ Predecessors' = [Predecessors EXCEPT ![self] = Predecessors[Predecessors[self]]]
                    /\ pc' = [pc EXCEPT ![self] = "finishCrashedNodeIsPredecessor"]
                    /\ UNCHANGED << msgQs, objLogs, allSubmittedWriteOps, 
                                    allSubmittedReadOps, terminatedYet, 
                                    nonInitClients, start, timeOracle, 
                                    Successors, currentHead, currentTail, 
                                    uninitializedObjs, initObj, objs_init, 
                                    obj_init, actions_init, action_init, 
                                    gateway_cinit, msg_cinit, uniqueId_cinit, 
                                    sentOps_init, recvdOps_init, crashNode, 
                                    objs, obj, actions, action, gateway_c, 
                                    msg_c, uniqueId, outstandingOps, 
                                    crashedNode, sender_zk, liveNode, req_z, 
                                    liveNodes, role, sender, req, pendingInvos, 
                                    failoverPendingInvos, now, 
                                    failoverUnpropagatedWrites, 
                                    failoverAckdWrites, version, pendingInvo >>

finishCrashedNodeIsPredecessor(self) == /\ pc[self] = "finishCrashedNodeIsPredecessor"
                                        /\ pc' = [pc EXCEPT ![self] = "failoverListen"]
                                        /\ UNCHANGED << msgQs, failoverMsgQs, 
                                                        objLogs, 
                                                        allSubmittedWriteOps, 
                                                        allSubmittedReadOps, 
                                                        terminatedYet, 
                                                        nonInitClients, start, 
                                                        timeOracle, Successors, 
                                                        Predecessors, 
                                                        currentHead, 
                                                        currentTail, 
                                                        uninitializedObjs, 
                                                        initObj, objs_init, 
                                                        obj_init, actions_init, 
                                                        action_init, 
                                                        gateway_cinit, 
                                                        msg_cinit, 
                                                        uniqueId_cinit, 
                                                        sentOps_init, 
                                                        recvdOps_init, 
                                                        crashNode, objs, obj, 
                                                        actions, action, 
                                                        gateway_c, msg_c, 
                                                        uniqueId, 
                                                        outstandingOps, 
                                                        crashedNode, sender_zk, 
                                                        liveNode, req_z, 
                                                        liveNodes, role, 
                                                        sender, req, 
                                                        pendingInvos, 
                                                        failoverPendingInvos, 
                                                        now, 
                                                        failoverUnpropagatedWrites, 
                                                        failoverAckdWrites, 
                                                        version, pendingInvo >>

failoverTailPropsLog(self) == /\ pc[self] = "failoverTailPropsLog"
                              /\ failoverMsgQs' = [failoverMsgQs EXCEPT ![<<self, (Successors[self])>>] = Append(@, ([  callType |-> FAILOVER_PROPAGATE_LOG,
                                                                                                                        log |-> objLogs[self]
                                                                                                                      ]))]
                              /\ pc' = [pc EXCEPT ![self] = "finishFailoverTailPropsLog"]
                              /\ UNCHANGED << msgQs, objLogs, 
                                              allSubmittedWriteOps, 
                                              allSubmittedReadOps, 
                                              terminatedYet, nonInitClients, 
                                              start, timeOracle, Successors, 
                                              Predecessors, currentHead, 
                                              currentTail, uninitializedObjs, 
                                              initObj, objs_init, obj_init, 
                                              actions_init, action_init, 
                                              gateway_cinit, msg_cinit, 
                                              uniqueId_cinit, sentOps_init, 
                                              recvdOps_init, crashNode, objs, 
                                              obj, actions, action, gateway_c, 
                                              msg_c, uniqueId, outstandingOps, 
                                              crashedNode, sender_zk, liveNode, 
                                              req_z, liveNodes, role, sender, 
                                              req, pendingInvos, 
                                              failoverPendingInvos, now, 
                                              failoverUnpropagatedWrites, 
                                              failoverAckdWrites, version, 
                                              pendingInvo >>

finishFailoverTailPropsLog(self) == /\ pc[self] = "finishFailoverTailPropsLog"
                                    /\ pc' = [pc EXCEPT ![self] = "failoverListen"]
                                    /\ UNCHANGED << msgQs, failoverMsgQs, 
                                                    objLogs, 
                                                    allSubmittedWriteOps, 
                                                    allSubmittedReadOps, 
                                                    terminatedYet, 
                                                    nonInitClients, start, 
                                                    timeOracle, Successors, 
                                                    Predecessors, currentHead, 
                                                    currentTail, 
                                                    uninitializedObjs, initObj, 
                                                    objs_init, obj_init, 
                                                    actions_init, action_init, 
                                                    gateway_cinit, msg_cinit, 
                                                    uniqueId_cinit, 
                                                    sentOps_init, 
                                                    recvdOps_init, crashNode, 
                                                    objs, obj, actions, action, 
                                                    gateway_c, msg_c, uniqueId, 
                                                    outstandingOps, 
                                                    crashedNode, sender_zk, 
                                                    liveNode, req_z, liveNodes, 
                                                    role, sender, req, 
                                                    pendingInvos, 
                                                    failoverPendingInvos, now, 
                                                    failoverUnpropagatedWrites, 
                                                    failoverAckdWrites, 
                                                    version, pendingInvo >>

failoverAssumeNewTail(self) == /\ pc[self] = "failoverAssumeNewTail"
                               /\ objLogs' = [objLogs EXCEPT ![self] = req[self].log]
                               /\ currentTail' = self
                               /\ pc' = [pc EXCEPT ![self] = "notifyZookeeper"]
                               /\ UNCHANGED << msgQs, failoverMsgQs, 
                                               allSubmittedWriteOps, 
                                               allSubmittedReadOps, 
                                               terminatedYet, nonInitClients, 
                                               start, timeOracle, Successors, 
                                               Predecessors, currentHead, 
                                               uninitializedObjs, initObj, 
                                               objs_init, obj_init, 
                                               actions_init, action_init, 
                                               gateway_cinit, msg_cinit, 
                                               uniqueId_cinit, sentOps_init, 
                                               recvdOps_init, crashNode, objs, 
                                               obj, actions, action, gateway_c, 
                                               msg_c, uniqueId, outstandingOps, 
                                               crashedNode, sender_zk, 
                                               liveNode, req_z, liveNodes, 
                                               role, sender, req, pendingInvos, 
                                               failoverPendingInvos, now, 
                                               failoverUnpropagatedWrites, 
                                               failoverAckdWrites, version, 
                                               pendingInvo >>

notifyZookeeper(self) == /\ pc[self] = "notifyZookeeper"
                         /\ msgQs' = [msgQs EXCEPT ![<<self, Zookeeper>>] = Append(@, ([ callType |-> ZK_CREATE]))]
                         /\ pc' = [pc EXCEPT ![self] = "finishFailoverAssumeNewTail"]
                         /\ UNCHANGED << failoverMsgQs, objLogs, 
                                         allSubmittedWriteOps, 
                                         allSubmittedReadOps, terminatedYet, 
                                         nonInitClients, start, timeOracle, 
                                         Successors, Predecessors, currentHead, 
                                         currentTail, uninitializedObjs, 
                                         initObj, objs_init, obj_init, 
                                         actions_init, action_init, 
                                         gateway_cinit, msg_cinit, 
                                         uniqueId_cinit, sentOps_init, 
                                         recvdOps_init, crashNode, objs, obj, 
                                         actions, action, gateway_c, msg_c, 
                                         uniqueId, outstandingOps, crashedNode, 
                                         sender_zk, liveNode, req_z, liveNodes, 
                                         role, sender, req, pendingInvos, 
                                         failoverPendingInvos, now, 
                                         failoverUnpropagatedWrites, 
                                         failoverAckdWrites, version, 
                                         pendingInvo >>

finishFailoverAssumeNewTail(self) == /\ pc[self] = "finishFailoverAssumeNewTail"
                                     /\ pc' = [pc EXCEPT ![self] = "failoverListen"]
                                     /\ UNCHANGED << msgQs, failoverMsgQs, 
                                                     objLogs, 
                                                     allSubmittedWriteOps, 
                                                     allSubmittedReadOps, 
                                                     terminatedYet, 
                                                     nonInitClients, start, 
                                                     timeOracle, Successors, 
                                                     Predecessors, currentHead, 
                                                     currentTail, 
                                                     uninitializedObjs, 
                                                     initObj, objs_init, 
                                                     obj_init, actions_init, 
                                                     action_init, 
                                                     gateway_cinit, msg_cinit, 
                                                     uniqueId_cinit, 
                                                     sentOps_init, 
                                                     recvdOps_init, crashNode, 
                                                     objs, obj, actions, 
                                                     action, gateway_c, msg_c, 
                                                     uniqueId, outstandingOps, 
                                                     crashedNode, sender_zk, 
                                                     liveNode, req_z, 
                                                     liveNodes, role, sender, 
                                                     req, pendingInvos, 
                                                     failoverPendingInvos, now, 
                                                     failoverUnpropagatedWrites, 
                                                     failoverAckdWrites, 
                                                     version, pendingInvo >>

crash(self) == /\ pc[self] = "crash"
               /\ msgQs' = [msgQs EXCEPT ![<<self, Zookeeper>>] = Append(@, ([ callType |-> ZK_SESSION_ENDED]))]
               /\ pc' = [pc EXCEPT ![self] = "zkConfigChanged"]
               /\ UNCHANGED << failoverMsgQs, objLogs, allSubmittedWriteOps, 
                               allSubmittedReadOps, terminatedYet, 
                               nonInitClients, start, timeOracle, Successors, 
                               Predecessors, currentHead, currentTail, 
                               uninitializedObjs, initObj, objs_init, obj_init, 
                               actions_init, action_init, gateway_cinit, 
                               msg_cinit, uniqueId_cinit, sentOps_init, 
                               recvdOps_init, crashNode, objs, obj, actions, 
                               action, gateway_c, msg_c, uniqueId, 
                               outstandingOps, crashedNode, sender_zk, 
                               liveNode, req_z, liveNodes, role, sender, req, 
                               pendingInvos, failoverPendingInvos, now, 
                               failoverUnpropagatedWrites, failoverAckdWrites, 
                               version, pendingInvo >>

zkConfigChanged(self) == /\ pc[self] = "zkConfigChanged"
                         /\ \E temp \in {s \in SendersTo(self): failoverMsgQs[<<s, self>>] /= << >>}:
                              sender' = [sender EXCEPT ![self] = temp]
                         /\ failoverMsgQs[<<sender'[self], self>>] /= << >>
                         /\ req' = [req EXCEPT ![self] = Head(failoverMsgQs[<<sender'[self], self>>])]
                         /\ failoverMsgQs' = [failoverMsgQs EXCEPT ![<<sender'[self], self>>] = Tail(@)]
                         /\ Assert((req'[self].callType = ZK_NODE_ADD), 
                                   "Failure of assertion at line 789, column 9.")
                         /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED << msgQs, objLogs, allSubmittedWriteOps, 
                                         allSubmittedReadOps, terminatedYet, 
                                         nonInitClients, start, timeOracle, 
                                         Successors, Predecessors, currentHead, 
                                         currentTail, uninitializedObjs, 
                                         initObj, objs_init, obj_init, 
                                         actions_init, action_init, 
                                         gateway_cinit, msg_cinit, 
                                         uniqueId_cinit, sentOps_init, 
                                         recvdOps_init, crashNode, objs, obj, 
                                         actions, action, gateway_c, msg_c, 
                                         uniqueId, outstandingOps, crashedNode, 
                                         sender_zk, liveNode, req_z, liveNodes, 
                                         role, pendingInvos, 
                                         failoverPendingInvos, now, 
                                         failoverUnpropagatedWrites, 
                                         failoverAckdWrites, version, 
                                         pendingInvo >>

n(self) == roleAssignment(self) \/ listen(self) \/ failoverListen(self)
              \/ handleReadInv(self) \/ apportionQ(self)
              \/ finishReadInv(self) \/ handleReadInvTail(self)
              \/ finishReadInvTail(self) \/ handleReadResp(self)
              \/ finishReadResp(self) \/ handleWriteInvHead(self)
              \/ finishWriteInvHead(self) \/ handleWriteInv(self)
              \/ finishWriteInv(self) \/ handleWriteInvTail(self)
              \/ tailAck(self) \/ finishWriteInvTail(self)
              \/ handleWriteResp(self) \/ finishWriteResp(self)
              \/ failoverCrashedNodeIsSuccessor(self)
              \/ finishCrashedNodeIsSuccessor(self)
              \/ failoverCrashedNodeIsPredecessor(self)
              \/ propagateFailedWrites(self) \/ backpropFailedAcks(self)
              \/ notifyTail(self) \/ finishCrashedNodeIsPredecessor(self)
              \/ failoverTailPropsLog(self)
              \/ finishFailoverTailPropsLog(self)
              \/ failoverAssumeNewTail(self) \/ notifyZookeeper(self)
              \/ finishFailoverAssumeNewTail(self) \/ crash(self)
              \/ zkConfigChanged(self)

Next == iclient \/ crasher \/ zk
           \/ (\E self \in nonInitClients: c(self))
           \/ (\E self \in Nodes: n(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ WF_vars(iclient)
        /\ WF_vars(crasher)
        /\ \A self \in nonInitClients : WF_vars(c(self))
        /\ WF_vars(zk)
        /\ \A self \in Nodes : WF_vars(n(self))

\* END TRANSLATION 


GlobalTypeInvariant ==  /\ msgQs \in [Network -> {<< >>} \cup Seq(RequestType)]
                        /\ objLogs \in [Nodes -> [Objects -> {<< >>} \cup Seq(ObjectVersionType)]]
\*                        /\ objTotalOrders \in [Objects -> Seq(RequestType)]
                        /\ allSubmittedWriteOps \in [Objects -> SUBSET(RequestType)]
                        /\ terminatedYet \in [Clients -> {TRUE, FALSE}]
                        /\ initClient \in Clients
                        /\ nonInitClients = Clients \ {initClient}
                        /\ start \in {TRUE, FALSE}
                        /\ timeOracle \in Nat
                        
                                            
InitClientTypeInvariant ==  /\ \A uninitObj \in uninitializedObjs: uninitObj \in Objects
                            /\ initObj \in Objects
                            /\ \A objInitd \in objs_init: objInitd \in Objects
                            /\ \A inv \in actions_init: inv \in {WRITE_INV, READ_INV}
                            /\ gateway_cinit \in Nodes \cup {NullNode}
                            /\ sentOps_init \in Nat
                            /\ recvdOps_init \in Nat
                            /\ msg_cinit \in RequestType \cup {NullReq}
                            /\ uniqueId_cinit \in UniqueIdType \cup {NullUniqueId}
                            
\*ClientTypeInvariant ==  \*/\ \A objInited \in objs: objInited \in [Clients -> Objects]
\*                        /\ obj \in [Clients \ {initClient} -> Objects]
\*                        /\ actions \in [Clients \ {initClient} -> SUBSET({WRITE_INV, READ_INV})]
\*                        /\ action \in [Clients \ {initClient} -> {WRITE_INV, READ_INV}]
\*                        /\ gateway_c \in [Clients \ {initClient} -> Nodes \cup {NullNode}]
\*                        /\ sentOps \in [Clients \ {initClient} -> Nat]
\*                        /\ recvdOps \in [Clients \ {initClient} -> Nat]
\*                        /\ msg_c \in [Clients \ {initClient} -> RequestType \cup {NullReq}]
\*                        /\ uniqueId \in [Clients \ {initClient} -> UniqueIdType]

                        
NodeTypeInvariant ==    /\ req \in [Nodes \ {head, tail} -> RequestType \cup {NullReq}]
                        /\ sender \in [Nodes \ {head, tail} -> Nodes \cup Clients \cup {NullNode}]
                        /\ now \in [Nodes \ {head, tail} -> Nat]
\*                        /\ pendingInvos \in [Nodes -> thisoneshard
                        
\*HeadTypeInvariant ==    /\ req_h \in RequestType \cup {NullReq}
\*                        /\ sender_h \in Nodes \cup Clients \cup {NullNode}
\*\*                        /\ pendingInvos_h \in thisoneshard
\*                        /\ now_h \in Nat
\*                        
\*TailTypeInvariant ==    /\ req_t \in RequestType \cup {NullReq}
\*                        /\ sender_t \in Nodes \cup Clients \cup {NullNode}
\*\*                        /\ pendingInvos_t \in thisoneshard
\*                        /\ now_t \in Nat

    
Writes(object) == allSubmittedWriteOps[object]
E_G(object) == {edge \in {<<w1, w2>> : w1, w2 \in Writes(object)}: edge[1].commitTs < edge[2].startTs}
Reads(object) == allSubmittedReadOps[object]

RECURSIVE ReduceSet(_, _, _)
ReduceSet(set, f(_, _), e) == IF set = {} THEN e ELSE 
                            LET chosen == CHOOSE rand \in set: TRUE 
                            IN f(chosen, ReduceSet(set \ {chosen}, f, e))

Graph(object) == LET    writes == Writes(object)
                        e_g == E_G(object)
                        reads == Reads(object) 
                 IN LET haonansAlgo(read, edges) == 
                        LET realtimeDep == edges \cup {<<write, read>>: write \in {w \in writes: w.commitTs < read.startTs}}
                            match == CHOOSE w \in writes: w.uniqueId = read.op.uniqueId 
                        IN  LET mergeReadIntoWrite == edges \cup { <<write, match>>: write \in {w \in writes: w.commitTs < read.startTs}}
                            IN  mergeReadIntoWrite \ {edge \in mergeReadIntoWrite: edge[1] = edge[2]}
                    IN  ReduceSet(reads, haonansAlgo, e_g)

                       
IsLinearizable == \A object \in Objects:    LET edges == Graph(object)
                                            IN \E e \in edges: (<<e[2], e[1]>> \in edges) = FALSE

                                
Terminated == \A client \in Clients: terminatedYet[client] = TRUE

Linearizability == IsLinearizable

=============================================================================
\* Modification History
\* Last modified Sun Sep 10 01:14:58 EDT 2023 by jenniferlam
\* Last modified Fri Sep 08 23:57:50 EDT 2023 by 72jen
\* Created Tue Jun 13 12:56:59 EDT 2023 by jenniferlam
