----------------------------- MODULE CRAQRetry -----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Clients, Nodes, head, tail, NumWrites, NumReads, Objects, MaxTimestamp, initClient, Zookeeper\*, newTail, crashedN 

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

EdgesFromClients == { <<c, n>> : c \in Clients, n \in Nodes}
EdgesToClients == { <<n, c>> : c \in Clients, n \in Nodes }
ClientEdges == EdgesFromClients \cup EdgesToClients

EdgesToZookeeper == { <<n, Zookeeper>> : n \in Nodes }
EdgesFromZookeeper == { <<Zookeeper, n>> : n \in Nodes }
ZookeeperEdges == EdgesToZookeeper \cup EdgesFromZookeeper

Network == Edges \cup ClientEdges \cup ZookeeperEdges

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
FAILOVER_PROPAGATE_LOG == "FAILOVER_PROPAGATE_LOG"


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
\*        IsCrashed(node) ==  LET crashed == CHOOSE c \in {ZK_SESSION_ENDED, NOTCRASHED}: TRUE 
\*                                IN crashed = ZK_SESSION_ENDED
        IsCrashed(node) == FALSE
        
        HasOutstandingWrites(node) == \A o \in Objects: LET log == objLogs[node][o]
                                                        IN  LET mostRecentVer == Head(log)
                                                            IN mostRecentVer.commitStatus = DIRTY
                                                            
        RECURSIVE ActiveNodes(_)
        ActiveNodes(node) ==    IF node = currentTail 
                                THEN {node} 
                                ELSE {node} \union ActiveNodes(Successors[node])
                                 
        RECURSIVE AcceptBackpropLog(_, _)
        AcceptBackpropLog(thatLog, thisLog) ==  IF thisLog = << >> \* if this log is empty
                                                THEN << >> \* then nothing could have been backpropped, nothing changes
                                                ELSE    LET thisMostRecentVer == Head(thisLog)
                                                        IN  IF thisMostRecentVer.commitStatus = CLEAN \* if this log is clean
                                                            THEN thisLog \* then we have nothing to add
                                                            ELSE    LET thatMostRecentVer == Head(thatLog) \* if this log has dirty writes
                                                                    \* and the backpropped log has the same write
                                                                    IN  IF  thisMostRecentVer.uniqueId = thatMostRecentVer.uniqueId
                                                                        THEN    IF thatMostRecentVer.commitStatus = DIRTY \* and that log is also dirty
                                                                                THEN thisLog  \* the two logs match, nothing more to change
                                                                                \* if that log is clean though, commit the write in this log
                                                                                \* and keep comparing matches between the rest of that log and this log
                                                                                ELSE Cons(thatMostRecentVer, AcceptBackpropLog(Tail(thatLog), Tail(thisLog)))
                                                                        \* if that log has an earlier version, keep backtracking through this log
                                                                        ELSE Cons(thisMostRecentVer, AcceptBackpropLog(thatLog, Tail(thisLog)))
        
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
        msg := Head(msgQs[<<sender, receiver>>]);
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
        crashNode := CHOOSE n \in ActiveNodes: n /= currentHead /\ n /= currentTail;
        send(crasher, crashNode, [callType |-> CRASH]);
    }
    
    fair process(c \in nonInitClients)
        variables   objs = Objects,
                    obj = NullObj,
                    actions = {WRITE_INV, READ_INV},
                    action = NullCall,
                    gateway_c = NullNode,
                    msg_c = NullReq,
                    uniqueId = <<self, 1>>,
                    sentOps = 0,
                    recvdOps = 0;
    {   
        waitForInit: when start = TRUE;
        concurrentOps: 
        while (objs /= {}) {
            obj := CHOOSE o \in objs: TRUE;
            objs := objs \ {obj};
            
            readOrWrite: 
            while (actions /= {}) {
                action := CHOOSE a \in actions: TRUE;
                actions := actions \ {action};
                
                send(   self, 
                        IF action = WRITE_INV THEN head ELSE CHOOSE n \in Nodes: n /= head, 
                        [   callType |-> action,
                            uniqueId |-> uniqueId,
                            startTs |-> NullTs,
                            commitTs |-> NullTs,
                            op |-> [obj |-> obj,
                                    uniqueId |-> uniqueId,
                                    writeStartTs |-> NullTs,
                                    writeCommitTs |-> NullTs,
                                    commitStatus |-> IF action = WRITE_INV 
                                                        THEN DIRTY 
                                                        ELSE NullCommitStatus]]);
                uniqueId := Increment(uniqueId);
                sentOps := sentOps + 1;
                
                waitForOps:
                while (recvdOps < sentOps) {
                    with (temp \in {s \in SendersTo(self): msgQs[<<s, self>>] /= << >>}) {
                        gateway_c := temp;
                    };
                    when msgQs[<<gateway_c, self>>] /= << >>; 
                    recv(gateway_c, self, msg_c); 
                    addToOpSet(msg_c);
                    assert(msg_c.uniqueId[1] = self);
                    recvdOps := recvdOps + 1;
                };
            };
            actions := {WRITE_INV, READ_INV}; 
        };
        
        terminate: terminatedYet[self] := TRUE;
    }
    
    fair process(zk="zookeeper")
        variables   crashedNode = NullNode,
                    liveNode = NullNode,
                    req_z = NullReq,
                    liveNodes = Nodes; 
    {
        listen_z: while (TRUE) {
            with (temp \in {s \in SendersTo(Zookeeper): msgQs[<<s, Zookeeper>>] /= << >>}) {
                crashedNode := temp;
            };
            
            when msgQs[<<crashedNode, Zookeeper>>] /= << >>;
            recv(crashedNode, Zookeeper, req_z); 
            
            if (req_z.callType = ZK_SESSION_ENDED) {
                triggerWatches:
                while (liveNodes /= {crashedNode}) {
                    liveNode := CHOOSE ln \in liveNodes: ln /= crashedNode;
                    send(Zookeeper, liveNode, [ callType    |-> ZK_NODE_DEL,
                                                crashedNode  |-> crashedNode]);
                    liveNodes := liveNodes \ {liveNode}
                }
                                        
            }
        }
    }
    
    fair process(n \in Nodes) 
        variables   role = MID,
                    sender = NullNode,
                    req = NullReq,
                    pendingInvos = {},
                    now = timeOracle;
                    
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
                                        if (Successors[self] = req.crashedNode) {
                                            goto failoverCrashedNodePredecessor;
\*                                        } else {
\*                                            if (Predecessors[self] = req.crashedNode) {
\*                                            }
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
        };
        
        
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
        
        handleReadResp:
        send(self, Find(pendingInvos, req.uniqueId), req);
        remove(pendingInvos, req.uniqueId);
        finishReadResp:
        goto listen;
        
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
        
        handleWriteInv:
        write(self, req.op);
        send(self, Successors[self], req);
        add(pendingInvos, req.uniqueId, sender);
        
        finishWriteInv:
        goto listen;
        
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
        
        handleWriteResp:
        objLogs[self][req.op.obj] := CommitDirtyVersion(@, req.op);
        send(self, Find(pendingInvos, req.uniqueId), req);
        remove(pendingInvos, req.uniqueId);
        
        finishWriteResp:
        goto listen;
        
        failoverCrashedNodePredecessor:
        if (HasOutstandingWrites(self)) {
            send(self, Successors[Successors[self]], [callType |-> FAILOVER_PROPAGATE_LOG]);
        };
        finishCrashedNodePredecessor:
        goto listen;
        
\*        handleCrashedNodeSuccessor:
        
        
        crash:
        now := -1; \* that's it, we crashed
    }
    
}

****************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "15f136c3" /\ chksum(tla) = "9d79a935")
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


IsCrashed(node) == FALSE

HasOutstandingWrites(node) == \A o \in Objects: LET log == objLogs[node][o]
                                                IN  LET mostRecentVer == Head(log)
                                                    IN mostRecentVer.commitStatus = DIRTY

RECURSIVE ActiveNodes(_)
ActiveNodes(node) ==    IF node = currentTail
                        THEN {node}
                        ELSE {node} \union ActiveNodes(Successors[node])

RECURSIVE AcceptBackpropLog(_, _)
AcceptBackpropLog(thatLog, thisLog) ==  IF thisLog = << >>
                                        THEN << >>
                                        ELSE    LET thisMostRecentVer == Head(thisLog)
                                                IN  IF thisMostRecentVer.commitStatus = CLEAN
                                                    THEN thisLog
                                                    ELSE    LET thatMostRecentVer == Head(thatLog)

                                                            IN  IF  thisMostRecentVer.uniqueId = thatMostRecentVer.uniqueId
                                                                THEN    IF thatMostRecentVer.commitStatus = DIRTY
                                                                        THEN thisLog


                                                                        ELSE Cons(thatMostRecentVer, AcceptBackpropLog(Tail(thatLog), Tail(thisLog)))

                                                                ELSE Cons(thisMostRecentVer, AcceptBackpropLog(thatLog, Tail(thisLog)))

VARIABLES uninitializedObjs, initObj, objs_init, obj_init, actions_init, 
          action_init, gateway_cinit, msg_cinit, uniqueId_cinit, sentOps_init, 
          recvdOps_init, objs, obj, actions, action, gateway_c, msg_c, 
          uniqueId, sentOps, recvdOps, crashedNode, liveNode, req_z, 
          liveNodes, role, sender, req, pendingInvos, now

vars == << msgQs, failoverMsgQs, objLogs, allSubmittedWriteOps, 
           allSubmittedReadOps, terminatedYet, nonInitClients, start, 
           timeOracle, Successors, Predecessors, currentHead, currentTail, pc, 
           uninitializedObjs, initObj, objs_init, obj_init, actions_init, 
           action_init, gateway_cinit, msg_cinit, uniqueId_cinit, 
           sentOps_init, recvdOps_init, objs, obj, actions, action, gateway_c, 
           msg_c, uniqueId, sentOps, recvdOps, crashedNode, liveNode, req_z, 
           liveNodes, role, sender, req, pendingInvos, now >>

ProcSet == {"initClient"} \cup (nonInitClients) \cup {"zookeeper"} \cup (Nodes)

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
        (* Process c *)
        /\ objs = [self \in nonInitClients |-> Objects]
        /\ obj = [self \in nonInitClients |-> NullObj]
        /\ actions = [self \in nonInitClients |-> {WRITE_INV, READ_INV}]
        /\ action = [self \in nonInitClients |-> NullCall]
        /\ gateway_c = [self \in nonInitClients |-> NullNode]
        /\ msg_c = [self \in nonInitClients |-> NullReq]
        /\ uniqueId = [self \in nonInitClients |-> <<self, 1>>]
        /\ sentOps = [self \in nonInitClients |-> 0]
        /\ recvdOps = [self \in nonInitClients |-> 0]
        (* Process zk *)
        /\ crashedNode = NullNode
        /\ liveNode = NullNode
        /\ req_z = NullReq
        /\ liveNodes = Nodes
        (* Process n *)
        /\ role = [self \in Nodes |-> MID]
        /\ sender = [self \in Nodes |-> NullNode]
        /\ req = [self \in Nodes |-> NullReq]
        /\ pendingInvos = [self \in Nodes |-> {}]
        /\ now = [self \in Nodes |-> timeOracle]
        /\ pc = [self \in ProcSet |-> CASE self = "initClient" -> "initializeObj"
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
                                 sentOps_init, recvdOps_init, objs, obj, 
                                 actions, action, gateway_c, msg_c, uniqueId, 
                                 sentOps, recvdOps, crashedNode, liveNode, 
                                 req_z, liveNodes, role, sender, req, 
                                 pendingInvos, now >>

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
                                recvdOps_init, objs, obj, actions, action, 
                                gateway_c, msg_c, uniqueId, sentOps, recvdOps, 
                                crashedNode, liveNode, req_z, liveNodes, role, 
                                sender, req, pendingInvos, now >>

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
                                      recvdOps_init, objs, obj, actions, 
                                      action, gateway_c, msg_c, uniqueId, 
                                      sentOps, recvdOps, crashedNode, liveNode, 
                                      req_z, liveNodes, role, sender, req, 
                                      pendingInvos, now >>

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
                                    recvdOps_init, objs, obj, actions, action, 
                                    gateway_c, msg_c, uniqueId, sentOps, 
                                    recvdOps, crashedNode, liveNode, req_z, 
                                    liveNodes, role, sender, req, pendingInvos, 
                                    now >>

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
                                   objs, obj, actions, action, gateway_c, 
                                   msg_c, uniqueId, sentOps, recvdOps, 
                                   crashedNode, liveNode, req_z, liveNodes, 
                                   role, sender, req, pendingInvos, now >>

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
                                  objs, obj, actions, action, gateway_c, msg_c, 
                                  uniqueId, sentOps, recvdOps, crashedNode, 
                                  liveNode, req_z, liveNodes, role, sender, 
                                  req, pendingInvos, now >>

iclient == initializeObj \/ waitFor_init \/ concurrentOps_init
              \/ readOrWrite_init \/ waitForOps_init \/ terminate_init

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
                                     sentOps_init, recvdOps_init, objs, obj, 
                                     actions, action, gateway_c, msg_c, 
                                     uniqueId, sentOps, recvdOps, crashedNode, 
                                     liveNode, req_z, liveNodes, role, sender, 
                                     req, pendingInvos, now >>

concurrentOps(self) == /\ pc[self] = "concurrentOps"
                       /\ IF objs[self] /= {}
                             THEN /\ obj' = [obj EXCEPT ![self] = CHOOSE o \in objs[self]: TRUE]
                                  /\ objs' = [objs EXCEPT ![self] = objs[self] \ {obj'[self]}]
                                  /\ pc' = [pc EXCEPT ![self] = "readOrWrite"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "terminate"]
                                  /\ UNCHANGED << objs, obj >>
                       /\ UNCHANGED << msgQs, failoverMsgQs, objLogs, 
                                       allSubmittedWriteOps, 
                                       allSubmittedReadOps, terminatedYet, 
                                       nonInitClients, start, timeOracle, 
                                       Successors, Predecessors, currentHead, 
                                       currentTail, uninitializedObjs, initObj, 
                                       objs_init, obj_init, actions_init, 
                                       action_init, gateway_cinit, msg_cinit, 
                                       uniqueId_cinit, sentOps_init, 
                                       recvdOps_init, actions, action, 
                                       gateway_c, msg_c, uniqueId, sentOps, 
                                       recvdOps, crashedNode, liveNode, req_z, 
                                       liveNodes, role, sender, req, 
                                       pendingInvos, now >>

readOrWrite(self) == /\ pc[self] = "readOrWrite"
                     /\ IF actions[self] /= {}
                           THEN /\ action' = [action EXCEPT ![self] = CHOOSE a \in actions[self]: TRUE]
                                /\ actions' = [actions EXCEPT ![self] = actions[self] \ {action'[self]}]
                                /\ msgQs' = [msgQs EXCEPT ![<<self, (IF action'[self] = WRITE_INV THEN head ELSE CHOOSE n \in Nodes: n /= head)>>] = Append(@, ([   callType |-> action'[self],
                                                                                                                                                                    uniqueId |-> uniqueId[self],
                                                                                                                                                                    startTs |-> NullTs,
                                                                                                                                                                    commitTs |-> NullTs,
                                                                                                                                                                    op |-> [obj |-> obj[self],
                                                                                                                                                                            uniqueId |-> uniqueId[self],
                                                                                                                                                                            writeStartTs |-> NullTs,
                                                                                                                                                                            writeCommitTs |-> NullTs,
                                                                                                                                                                            commitStatus |-> IF action'[self] = WRITE_INV
                                                                                                                                                                                                THEN DIRTY
                                                                                                                                                                                                ELSE NullCommitStatus]]))]
                                /\ uniqueId' = [uniqueId EXCEPT ![self] = Increment(uniqueId[self])]
                                /\ sentOps' = [sentOps EXCEPT ![self] = sentOps[self] + 1]
                                /\ pc' = [pc EXCEPT ![self] = "waitForOps"]
                           ELSE /\ actions' = [actions EXCEPT ![self] = {WRITE_INV, READ_INV}]
                                /\ pc' = [pc EXCEPT ![self] = "concurrentOps"]
                                /\ UNCHANGED << msgQs, action, uniqueId, 
                                                sentOps >>
                     /\ UNCHANGED << failoverMsgQs, objLogs, 
                                     allSubmittedWriteOps, allSubmittedReadOps, 
                                     terminatedYet, nonInitClients, start, 
                                     timeOracle, Successors, Predecessors, 
                                     currentHead, currentTail, 
                                     uninitializedObjs, initObj, objs_init, 
                                     obj_init, actions_init, action_init, 
                                     gateway_cinit, msg_cinit, uniqueId_cinit, 
                                     sentOps_init, recvdOps_init, objs, obj, 
                                     gateway_c, msg_c, recvdOps, crashedNode, 
                                     liveNode, req_z, liveNodes, role, sender, 
                                     req, pendingInvos, now >>

waitForOps(self) == /\ pc[self] = "waitForOps"
                    /\ IF recvdOps[self] < sentOps[self]
                          THEN /\ \E temp \in {s \in SendersTo(self): msgQs[<<s, self>>] /= << >>}:
                                    gateway_c' = [gateway_c EXCEPT ![self] = temp]
                               /\ msgQs[<<gateway_c'[self], self>>] /= << >>
                               /\ msg_c' = [msg_c EXCEPT ![self] = Head(msgQs[<<gateway_c'[self], self>>])]
                               /\ msgQs' = [msgQs EXCEPT ![<<gateway_c'[self], self>>] = Tail(@)]
                               /\ IF msg_c'[self].callType = WRITE_RESP
                                     THEN /\ allSubmittedWriteOps' = [allSubmittedWriteOps EXCEPT ![msg_c'[self].op.obj] = allSubmittedWriteOps[msg_c'[self].op.obj] \cup {msg_c'[self]}]
                                          /\ UNCHANGED allSubmittedReadOps
                                     ELSE /\ allSubmittedReadOps' = [allSubmittedReadOps EXCEPT ![msg_c'[self].op.obj] = allSubmittedReadOps[msg_c'[self].op.obj] \cup {msg_c'[self]}]
                                          /\ UNCHANGED allSubmittedWriteOps
                               /\ Assert((msg_c'[self].uniqueId[1] = self), 
                                         "Failure of assertion at line 350, column 21.")
                               /\ recvdOps' = [recvdOps EXCEPT ![self] = recvdOps[self] + 1]
                               /\ pc' = [pc EXCEPT ![self] = "waitForOps"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "readOrWrite"]
                               /\ UNCHANGED << msgQs, allSubmittedWriteOps, 
                                               allSubmittedReadOps, gateway_c, 
                                               msg_c, recvdOps >>
                    /\ UNCHANGED << failoverMsgQs, objLogs, terminatedYet, 
                                    nonInitClients, start, timeOracle, 
                                    Successors, Predecessors, currentHead, 
                                    currentTail, uninitializedObjs, initObj, 
                                    objs_init, obj_init, actions_init, 
                                    action_init, gateway_cinit, msg_cinit, 
                                    uniqueId_cinit, sentOps_init, 
                                    recvdOps_init, objs, obj, actions, action, 
                                    uniqueId, sentOps, crashedNode, liveNode, 
                                    req_z, liveNodes, role, sender, req, 
                                    pendingInvos, now >>

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
                                   objs, obj, actions, action, gateway_c, 
                                   msg_c, uniqueId, sentOps, recvdOps, 
                                   crashedNode, liveNode, req_z, liveNodes, 
                                   role, sender, req, pendingInvos, now >>

c(self) == waitForInit(self) \/ concurrentOps(self) \/ readOrWrite(self)
              \/ waitForOps(self) \/ terminate(self)

listen_z == /\ pc["zookeeper"] = "listen_z"
            /\ \E temp \in {s \in SendersTo(Zookeeper): msgQs[<<s, Zookeeper>>] /= << >>}:
                 crashedNode' = temp
            /\ msgQs[<<crashedNode', Zookeeper>>] /= << >>
            /\ req_z' = Head(msgQs[<<crashedNode', Zookeeper>>])
            /\ msgQs' = [msgQs EXCEPT ![<<crashedNode', Zookeeper>>] = Tail(@)]
            /\ IF req_z'.callType = ZK_SESSION_ENDED
                  THEN /\ pc' = [pc EXCEPT !["zookeeper"] = "triggerWatches"]
                  ELSE /\ pc' = [pc EXCEPT !["zookeeper"] = "listen_z"]
            /\ UNCHANGED << failoverMsgQs, objLogs, allSubmittedWriteOps, 
                            allSubmittedReadOps, terminatedYet, nonInitClients, 
                            start, timeOracle, Successors, Predecessors, 
                            currentHead, currentTail, uninitializedObjs, 
                            initObj, objs_init, obj_init, actions_init, 
                            action_init, gateway_cinit, msg_cinit, 
                            uniqueId_cinit, sentOps_init, recvdOps_init, objs, 
                            obj, actions, action, gateway_c, msg_c, uniqueId, 
                            sentOps, recvdOps, liveNode, liveNodes, role, 
                            sender, req, pendingInvos, now >>

triggerWatches == /\ pc["zookeeper"] = "triggerWatches"
                  /\ IF liveNodes /= {crashedNode}
                        THEN /\ liveNode' = (CHOOSE ln \in liveNodes: ln /= crashedNode)
                             /\ msgQs' = [msgQs EXCEPT ![<<Zookeeper, liveNode'>>] = Append(@, ([ callType    |-> ZK_NODE_DEL,
                                                                                                  crashedNode  |-> crashedNode]))]
                             /\ liveNodes' = liveNodes \ {liveNode'}
                             /\ pc' = [pc EXCEPT !["zookeeper"] = "triggerWatches"]
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
                                  objs, obj, actions, action, gateway_c, msg_c, 
                                  uniqueId, sentOps, recvdOps, crashedNode, 
                                  req_z, role, sender, req, pendingInvos, now >>

zk == listen_z \/ triggerWatches

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
                                        recvdOps_init, objs, obj, actions, 
                                        action, gateway_c, msg_c, uniqueId, 
                                        sentOps, recvdOps, crashedNode, 
                                        liveNode, req_z, liveNodes, sender, 
                                        req, pendingInvos, now >>

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
                                                                                        THEN /\ IF Successors[self] = req'[self].crashedNode
                                                                                                   THEN /\ pc' = [pc EXCEPT ![self] = "failoverCrashedNodePredecessor"]
                                                                                                   ELSE /\ pc' = [pc EXCEPT ![self] = "listen"]
                                                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "listen"]
                      ELSE /\ IF role[self] = TAIL
                                 THEN /\ IF req'[self].callType = READ_INV
                                            THEN /\ pc' = [pc EXCEPT ![self] = "handleReadInvTail"]
                                            ELSE /\ IF req'[self].callType = WRITE_INV
                                                       THEN /\ pc' = [pc EXCEPT ![self] = "handleWriteInvTail"]
                                                       ELSE /\ IF req'[self].callType = CRASH
                                                                  THEN /\ pc' = [pc EXCEPT ![self] = "crash"]
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
                                                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "listen"]
                /\ UNCHANGED << failoverMsgQs, objLogs, allSubmittedWriteOps, 
                                allSubmittedReadOps, terminatedYet, 
                                nonInitClients, start, timeOracle, Successors, 
                                Predecessors, currentHead, currentTail, 
                                uninitializedObjs, initObj, objs_init, 
                                obj_init, actions_init, action_init, 
                                gateway_cinit, msg_cinit, uniqueId_cinit, 
                                sentOps_init, recvdOps_init, objs, obj, 
                                actions, action, gateway_c, msg_c, uniqueId, 
                                sentOps, recvdOps, crashedNode, liveNode, 
                                req_z, liveNodes, role, pendingInvos, now >>

failoverListen(self) == /\ pc[self] = "failoverListen"
                        /\ \E temp \in {s \in SendersTo(self): failoverMsgQs[<<s, self>>] /= << >>}:
                             sender' = [sender EXCEPT ![self] = temp]
                        /\ pc' = [pc EXCEPT ![self] = "failoverListen"]
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
                                        recvdOps_init, objs, obj, actions, 
                                        action, gateway_c, msg_c, uniqueId, 
                                        sentOps, recvdOps, crashedNode, 
                                        liveNode, req_z, liveNodes, role, req, 
                                        pendingInvos, now >>

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
                                       recvdOps_init, objs, obj, actions, 
                                       action, gateway_c, msg_c, uniqueId, 
                                       sentOps, recvdOps, crashedNode, 
                                       liveNode, req_z, liveNodes, role, 
                                       sender, pendingInvos >>

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
                                    sentOps_init, recvdOps_init, objs, obj, 
                                    actions, action, gateway_c, msg_c, 
                                    uniqueId, sentOps, recvdOps, crashedNode, 
                                    liveNode, req_z, liveNodes, role, sender, 
                                    req, now >>

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
                                       recvdOps_init, objs, obj, actions, 
                                       action, gateway_c, msg_c, uniqueId, 
                                       sentOps, recvdOps, crashedNode, 
                                       liveNode, req_z, liveNodes, role, 
                                       sender, req, pendingInvos, now >>

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
                                           recvdOps_init, objs, obj, actions, 
                                           action, gateway_c, msg_c, uniqueId, 
                                           sentOps, recvdOps, crashedNode, 
                                           liveNode, req_z, liveNodes, role, 
                                           sender, pendingInvos >>

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
                                           sentOps_init, recvdOps_init, objs, 
                                           obj, actions, action, gateway_c, 
                                           msg_c, uniqueId, sentOps, recvdOps, 
                                           crashedNode, liveNode, req_z, 
                                           liveNodes, role, sender, req, 
                                           pendingInvos, now >>

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
                                        recvdOps_init, objs, obj, actions, 
                                        action, gateway_c, msg_c, uniqueId, 
                                        sentOps, recvdOps, crashedNode, 
                                        liveNode, req_z, liveNodes, role, 
                                        sender, req, now >>

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
                                        recvdOps_init, objs, obj, actions, 
                                        action, gateway_c, msg_c, uniqueId, 
                                        sentOps, recvdOps, crashedNode, 
                                        liveNode, req_z, liveNodes, role, 
                                        sender, req, pendingInvos, now >>

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
                                            recvdOps_init, objs, obj, actions, 
                                            action, gateway_c, msg_c, uniqueId, 
                                            sentOps, recvdOps, crashedNode, 
                                            liveNode, req_z, liveNodes, role, 
                                            sender >>

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
                                            sentOps_init, recvdOps_init, objs, 
                                            obj, actions, action, gateway_c, 
                                            msg_c, uniqueId, sentOps, recvdOps, 
                                            crashedNode, liveNode, req_z, 
                                            liveNodes, role, sender, req, 
                                            pendingInvos, now >>

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
                                        recvdOps_init, objs, obj, actions, 
                                        action, gateway_c, msg_c, uniqueId, 
                                        sentOps, recvdOps, crashedNode, 
                                        liveNode, req_z, liveNodes, role, 
                                        sender, req, now >>

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
                                        recvdOps_init, objs, obj, actions, 
                                        action, gateway_c, msg_c, uniqueId, 
                                        sentOps, recvdOps, crashedNode, 
                                        liveNode, req_z, liveNodes, role, 
                                        sender, req, pendingInvos, now >>

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
                                            recvdOps_init, objs, obj, actions, 
                                            action, gateway_c, msg_c, uniqueId, 
                                            sentOps, recvdOps, crashedNode, 
                                            liveNode, req_z, liveNodes, role, 
                                            sender, req, pendingInvos >>

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
                                 sentOps_init, recvdOps_init, objs, obj, 
                                 actions, action, gateway_c, msg_c, uniqueId, 
                                 sentOps, recvdOps, crashedNode, liveNode, 
                                 req_z, liveNodes, role, sender, pendingInvos, 
                                 now >>

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
                                            sentOps_init, recvdOps_init, objs, 
                                            obj, actions, action, gateway_c, 
                                            msg_c, uniqueId, sentOps, recvdOps, 
                                            crashedNode, liveNode, req_z, 
                                            liveNodes, role, sender, req, 
                                            pendingInvos, now >>

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
                                         recvdOps_init, objs, obj, actions, 
                                         action, gateway_c, msg_c, uniqueId, 
                                         sentOps, recvdOps, crashedNode, 
                                         liveNode, req_z, liveNodes, role, 
                                         sender, req, now >>

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
                                         recvdOps_init, objs, obj, actions, 
                                         action, gateway_c, msg_c, uniqueId, 
                                         sentOps, recvdOps, crashedNode, 
                                         liveNode, req_z, liveNodes, role, 
                                         sender, req, pendingInvos, now >>

failoverCrashedNodePredecessor(self) == /\ pc[self] = "failoverCrashedNodePredecessor"
                                        /\ IF HasOutstandingWrites(self)
                                              THEN /\ msgQs' = [msgQs EXCEPT ![<<self, (Successors[Successors[self]])>>] = Append(@, ([callType |-> FAILOVER_PROPAGATE_LOG]))]
                                              ELSE /\ TRUE
                                                   /\ msgQs' = msgQs
                                        /\ pc' = [pc EXCEPT ![self] = "finishCrashedNodePredecessor"]
                                        /\ UNCHANGED << failoverMsgQs, objLogs, 
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
                                                        recvdOps_init, objs, 
                                                        obj, actions, action, 
                                                        gateway_c, msg_c, 
                                                        uniqueId, sentOps, 
                                                        recvdOps, crashedNode, 
                                                        liveNode, req_z, 
                                                        liveNodes, role, 
                                                        sender, req, 
                                                        pendingInvos, now >>

finishCrashedNodePredecessor(self) == /\ pc[self] = "finishCrashedNodePredecessor"
                                      /\ pc' = [pc EXCEPT ![self] = "listen"]
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
                                                      recvdOps_init, objs, obj, 
                                                      actions, action, 
                                                      gateway_c, msg_c, 
                                                      uniqueId, sentOps, 
                                                      recvdOps, crashedNode, 
                                                      liveNode, req_z, 
                                                      liveNodes, role, sender, 
                                                      req, pendingInvos, now >>

crash(self) == /\ pc[self] = "crash"
               /\ now' = [now EXCEPT ![self] = -1]
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << msgQs, failoverMsgQs, objLogs, 
                               allSubmittedWriteOps, allSubmittedReadOps, 
                               terminatedYet, nonInitClients, start, 
                               timeOracle, Successors, Predecessors, 
                               currentHead, currentTail, uninitializedObjs, 
                               initObj, objs_init, obj_init, actions_init, 
                               action_init, gateway_cinit, msg_cinit, 
                               uniqueId_cinit, sentOps_init, recvdOps_init, 
                               objs, obj, actions, action, gateway_c, msg_c, 
                               uniqueId, sentOps, recvdOps, crashedNode, 
                               liveNode, req_z, liveNodes, role, sender, req, 
                               pendingInvos >>

n(self) == roleAssignment(self) \/ listen(self) \/ failoverListen(self)
              \/ handleReadInv(self) \/ apportionQ(self)
              \/ finishReadInv(self) \/ handleReadInvTail(self)
              \/ finishReadInvTail(self) \/ handleReadResp(self)
              \/ finishReadResp(self) \/ handleWriteInvHead(self)
              \/ finishWriteInvHead(self) \/ handleWriteInv(self)
              \/ finishWriteInv(self) \/ handleWriteInvTail(self)
              \/ tailAck(self) \/ finishWriteInvTail(self)
              \/ handleWriteResp(self) \/ finishWriteResp(self)
              \/ failoverCrashedNodePredecessor(self)
              \/ finishCrashedNodePredecessor(self) \/ crash(self)

Next == iclient \/ zk
           \/ (\E self \in nonInitClients: c(self))
           \/ (\E self \in Nodes: n(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ WF_vars(iclient)
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
                            
ClientTypeInvariant ==  \*/\ \A objInited \in objs: objInited \in [Clients -> Objects]
                        /\ obj \in [Clients \ {initClient} -> Objects]
                        /\ actions \in [Clients \ {initClient} -> SUBSET({WRITE_INV, READ_INV})]
                        /\ action \in [Clients \ {initClient} -> {WRITE_INV, READ_INV}]
                        /\ gateway_c \in [Clients \ {initClient} -> Nodes \cup {NullNode}]
                        /\ sentOps \in [Clients \ {initClient} -> Nat]
                        /\ recvdOps \in [Clients \ {initClient} -> Nat]
                        /\ msg_c \in [Clients \ {initClient} -> RequestType \cup {NullReq}]
                        /\ uniqueId \in [Clients \ {initClient} -> UniqueIdType]

                        
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
\* Last modified Fri Sep 08 23:57:50 EDT 2023 by 72jen
\* Last modified Fri Sep 08 18:14:59 EDT 2023 by jenniferlam
\* Created Tue Jun 13 12:56:59 EDT 2023 by jenniferlam
