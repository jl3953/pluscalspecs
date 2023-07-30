----------------------------- MODULE CRAQRetry -----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Clients, Nodes, head, crashedN, tail, newTail, NumWrites, NumReads, Objects, MaxTimestamp, initClient, Zookeeper

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

CRASHED == "CRASHED"
NOTCRASHED == "NOTCRASHED"

NODE_DEL == "NODE_DEL"

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
                objLogs = [n \in Nodes |-> [o \in Objects |-> << >>]],
                allSubmittedWriteOps = [o \in Objects |-> {}],
                allSubmittedReadOps = [ o \in Objects |-> {}],
                terminatedYet = [c \in Clients |-> FALSE],
                nonInitClients = Clients \ {initClient},
                start = FALSE,
                timeOracle = 10,
                Successors = [n \in Nodes |-> LET e == CHOOSE edge \in NextEdges : edge[1] = n IN e[2]],
                Predecessors = [n \in Nodes |-> LET e == CHOOSE edge \in PrevEdges : edge[1] = n IN e[2]]
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
\*        IsCrashed(node) ==  LET crashed == CHOOSE c \in {CRASHED, NOTCRASHED}: TRUE 
\*                                IN crashed = CRASHED
        IsCrashed(node) == FALSE
        
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
    
    macro recv(sender, receiver, msg) {
        msg := Head(msgQs[<<sender, receiver>>]);
        msgQs[<<sender, receiver>>] := Tail(@);
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
        neverstart: when FALSE;
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
            
            if (req_z.callType = CRASHED) {
                triggerWatches:
                while (liveNodes /= {crashedNode}) {
                    liveNode := CHOOSE ln \in liveNodes: ln /= crashedNode;
                    send(Zookeeper, liveNode, [ callType    |-> NODE_DEL,
                                                crashedNode  |-> crashedNode]);
                    liveNodes := liveNodes \ {liveNode}
                }
                                        
            }
        }
    }
    
    fair process(he="head") 
        variables req_h = NullReq,
                  sender_h = NullNode,
                  pendingInvos_h = {},
                  now_h = timeOracle,
                  allObjs = Objects;
    {
        listen_h: while (TRUE) {
            with (temp \in {s \in SendersTo(head): msgQs[<<s, head>>] /= << >>}) {
                sender_h := temp;
            }; 
            
            when msgQs[<<sender_h, head>>] /= << >>;  
            recv(sender_h, head, req_h);
            if (req_h.callType = READ_INV) {
                if (IsDirty(head, req_h.op.obj)) {
                    apportionQ_h: send(head, tail, req_h);
                    add(pendingInvos_h, req_h.uniqueId, sender_h);
                } else {
                    now_h := timeOracle;
                    timeOracle := timeOracle + 1;
                    respFromHead: req_h := [ callType |-> READ_RESP,
                                            uniqueId |-> req_h.uniqueId,
                                            startTs |-> timeOracle,
                                            commitTs |-> timeOracle,
                                            op |-> Read(head, req_h.op.obj)];
                    send(head, sender_h, req_h);
                }
            } else {
                if (req_h.callType = READ_RESP) {
                    readResp_h: send(head, Find(pendingInvos_h, req_h.uniqueId), req_h);
                    remove(pendingInvos_h, req_h.uniqueId);
                } else {
                    if (req_h.callType = WRITE_INV) {
                        now_h := timeOracle;
                        timeOracle := timeOracle + 1;
                        dirtyWrite_h: req_h := [req_h EXCEPT    !.startTs = now_h,
                                                                !.op.writeStartTs = now_h,
                                                                !.op.commitStatus = DIRTY];
                        write(head, req_h.op);
                        send(head, Successors[head], req_h);
                        add(pendingInvos_h, req_h.uniqueId, sender_h);
                    } else { 
                        if (req_h.callType = WRITE_RESP) {\* WRITE_RESP
                            objLogs[head][req_h.op.obj] := CommitDirtyVersion(@, req_h.op);
                            respToClient: send(head, Find(pendingInvos_h, req_h.uniqueId), req_h);
                            remove(pendingInvos_h, req_h.uniqueId);
                        } else {
                            if (req_h.callType = NODE_DEL) {
                                if (req_h.crashedNode = Successors[head]) {
                                    
                                    \* Change successor
                                    Successors[head] := Successors[Successors[head]];
\*                                    Successors[Successors[head]] := nil;
                                    
                                    \* Propagate outstanding writes
\*                                    send(head, Successors[head], [callType |-> FWDPROP_LOG]);
                                }
                            } \*else {
\*                                if (req_h.callType = BACKPROP_LOG) {
\*                                    allObjs := Objects;
\*                                    while (allObjs /= {}) {
\*                                        o := CHOOSE obj \in allObjs: TRUE
\*                                        objLog[head][o] := AcceptBackpropLog(objLogs[sender_h][o], objLog[head][o]);
\*                                        allObjs := allObjs \ {o}
\*                                    }
\*                                }
                            
\*                            } \* BACKPROP_LOG
                        } \* NODE_DEL
                    } \* WRITE_RESP
                } \* WRITE_INV
            } \* READ_RESP
        } \* listen_h: while (TRUE)
    } \* process
    
    fair process(ta="tail")
        variables   req_t = NullReq,
                    sender_t = NullNode,
                    pendingInvos_t = {},
                    now_t = timeOracle;
    {
        listen_t: while (TRUE) {
            with (temp \in {s \in SendersTo(tail) : msgQs[<<s, tail>>] /= << >>}) {
                sender_t := temp;
            };
            
            when msgQs[<<sender_t, tail>>] /= << >>;  
            recv(sender_t, tail, req_t);
            if (req_t.callType = READ_INV) {
                now_t := timeOracle;
                timeOracle := timeOracle + 1;
                respFromSelf_t: req_t := [ callType |-> READ_RESP,
                                        uniqueId |-> req_t.uniqueId,
                                        startTs |-> now_t,
                                        commitTs |-> now_t,
                                        op |-> Read(tail, req_t.op.obj)];
                send(tail, sender_t, req_t);
            } else { 
                if (req_t.callType = WRITE_INV) {
                    now_t := timeOracle;
                    timeOracle := timeOracle + 1;
                    write(tail, [req_t.op EXCEPT    !.writeCommitTs = now_t, 
                                                    !.commitStatus = CLEAN]);
                    tailAck: req_t := [ callType |-> WRITE_RESP,
                                        uniqueId |-> req_t.uniqueId,
                                        startTs |-> req_t.startTs,
                                        commitTs |-> Read(tail, req_t.op.obj).writeCommitTs,
                                        op |-> Read(tail, req_t.op.obj)];
                    send(tail, Predecessors[tail], req_t);
                } else { \* CRASH
                    if (req_t.callType = NODE_DEL) {
                        if (req_t.crashedNode = Predecessors[tail]) {
                        
                            \* change predecessor to predecessor's predecessor
                            Predecessors[tail] := Predecessors[Predecessors[tail]];
\*                            Predecessors[Predecessors[tail]] := nil;
                            
                            \* backpropagate stuff
\*                            send(tail, Predecessors[tail], [callType |-> BACKPROP_LOG]);
                            
                            \* propagates objects to new tail
\*                            send(tail, Successors[tail], [callType |-> FWDPROP_LOG]);
                            
                            \* switches roles
                            goto rolenode;
                        }
                    } \*else {
\*                        if (req_t.callType = FWDPROP_LOG) {
\*                            
\*                        }
\*                    } \* FWDPROP_LOG
                } \* NODE_DEL
            } \* WRITE_INV
        }; \* listen_t while (TRUE)
        
        rolenode: while (TRUE) {
            with (temp \in {s \in SendersTo(tail) : msgQs[<<s, tail>>] /= << >>}) {
                sender := temp;
            };
            
            when msgQs[<<sender, tail>>] /= << >>;  
            recv(sender, tail, req); 
            
            if (req.callType = READ_INV) {
                if (IsDirty(tail, req.op.obj)) {                 
                    apportionQ: send(tail, newTail, req);
                    add(pendingInvos, req.uniqueId, sender);
                } else {
                    now := timeOracle;
                    timeOracle := timeOracle + 1;
                    respFromSelf: req :=  [callType |-> READ_RESP,
                                        uniqueId |-> req.uniqueId,
                                        startTs |-> now,
                                        commitTs |-> now,
                                        op |-> Read(tail, req.op.obj)];
                    send(tail, sender, req);
                } 
            } else {
                if (req.callType = READ_RESP) {
                    fwdFromTail: send(tail, Find(pendingInvos, req.uniqueId), req);
                    remove(pendingInvos, req.uniqueId);
                } else { 
                    if (req.callType = WRITE_INV) {
                        write(tail, req.op);
                        propagate: send(tail, Successors[tail], req);
                        add(pendingInvos, req.uniqueId, sender);
                    } else { \* WRITE_RESP
                        objLogs[tail][req.op.obj] := CommitDirtyVersion(@, req.op);
                        backProp: send(tail, Find(pendingInvos, req.uniqueId), req);
                        remove(pendingInvos, req.uniqueId);
                    }
                }
            }  
        };
    }
    
    fair process(n \in Nodes \ {head, tail, newTail})
        variables   req = NullReq,
                    sender = NullNode,
                    now = timeOracle, 
                    pendingInvos = {};
    {
        tempCrash: goto crash;
        
        listen: while (TRUE) {
            with (temp \in {s \in SendersTo(self) : msgQs[<<s, self>>] /= << >>}) {
                sender := temp;
            };
            
            when msgQs[<<sender, self>>] /= << >>;  
            recv(sender, self, req); 
            
            if (req.callType = READ_INV) {
                if (IsDirty(self, req.op.obj)) {
                    if (IsCrashed(self)) {
                        goto crash;
                    };                 
                    apportionQ: send(self, tail, req);
                    if (IsCrashed(self)) {
                        goto crash;
                    };
                    crashLabel: add(pendingInvos, req.uniqueId, sender);
                } else {
                    now := timeOracle;
                    timeOracle := timeOracle + 1;
                    respFromSelf: req :=  [callType |-> READ_RESP,
                                        uniqueId |-> req.uniqueId,
                                        startTs |-> now,
                                        commitTs |-> now,
                                        op |-> Read(self, req.op.obj)];
                    if (IsCrashed(self)) {
                        goto crash;
                    };
                    sendLabel: send(self, sender, req);
                    if (IsCrashed(self)) {
                        goto crash;
                    };
                } 
            } else {
                if (req.callType = READ_RESP) {
                    if (IsCrashed(self)) {
                        goto crash;
                    };
                    fwdFromTail: send(self, Find(pendingInvos, req.uniqueId), req);
                    crashLabelReadResp: if (IsCrashed(self)) {
                        goto crash;
                    };
                    removeLabel: remove(pendingInvos, req.uniqueId);
                } else { 
                    if (req.callType = WRITE_INV) {
                        write(self, req.op);
                        if (IsCrashed(self)) {
                            goto crash;
                        };
                        propagate: send(self, Successors[self], req);
                        add(pendingInvos, req.uniqueId, sender);
                        crashLabelWriteInv: if (IsCrashed(self)) {
                            goto crash;
                        };
                    } else { \* WRITE_RESP
                        
                        objLogs[self][req.op.obj] := CommitDirtyVersion(@, req.op);
                        if (IsCrashed(self)) {
                            goto crash;
                        };
                        backProp: send(self, Find(pendingInvos, req.uniqueId), req);
                        remove(pendingInvos, req.uniqueId);
                         
                        crashLabelWriteResp: 
                        if (IsCrashed(self)) {
                            goto crash;
                        }
                    }
                }
            }  
        };
        
        crash: send(self, Zookeeper, [ callType |-> CRASHED ]);
    }
}

****************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "1c319ef8" /\ chksum(tla) = "76b5d529")
\* Label apportionQ of process ta at line 160 col 9 changed to apportionQ_
\* Label respFromSelf of process ta at line 503 col 35 changed to respFromSelf_
\* Label fwdFromTail of process ta at line 160 col 9 changed to fwdFromTail_
\* Label propagate of process ta at line 160 col 9 changed to propagate_
\* Label backProp of process ta at line 160 col 9 changed to backProp_
VARIABLES msgQs, objLogs, allSubmittedWriteOps, allSubmittedReadOps, 
          terminatedYet, nonInitClients, start, timeOracle, Successors, 
          Predecessors, pc

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
          liveNodes, req_h, sender_h, pendingInvos_h, now_h, allObjs, req_t, 
          sender_t, pendingInvos_t, now_t, req, sender, now, pendingInvos

vars == << msgQs, objLogs, allSubmittedWriteOps, allSubmittedReadOps, 
           terminatedYet, nonInitClients, start, timeOracle, Successors, 
           Predecessors, pc, uninitializedObjs, initObj, objs_init, obj_init, 
           actions_init, action_init, gateway_cinit, msg_cinit, 
           uniqueId_cinit, sentOps_init, recvdOps_init, objs, obj, actions, 
           action, gateway_c, msg_c, uniqueId, sentOps, recvdOps, crashedNode, 
           liveNode, req_z, liveNodes, req_h, sender_h, pendingInvos_h, now_h, 
           allObjs, req_t, sender_t, pendingInvos_t, now_t, req, sender, now, 
           pendingInvos >>

ProcSet == {"initClient"} \cup (nonInitClients) \cup {"zookeeper"} \cup {"head"} \cup {"tail"} \cup (Nodes \ {head, tail, newTail})

Init == (* Global variables *)
        /\ msgQs = [edge \in Network |-> << >>]
        /\ objLogs = [n \in Nodes |-> [o \in Objects |-> << >>]]
        /\ allSubmittedWriteOps = [o \in Objects |-> {}]
        /\ allSubmittedReadOps = [ o \in Objects |-> {}]
        /\ terminatedYet = [c \in Clients |-> FALSE]
        /\ nonInitClients = Clients \ {initClient}
        /\ start = FALSE
        /\ timeOracle = 10
        /\ Successors = [n \in Nodes |-> LET e == CHOOSE edge \in NextEdges : edge[1] = n IN e[2]]
        /\ Predecessors = [n \in Nodes |-> LET e == CHOOSE edge \in PrevEdges : edge[1] = n IN e[2]]
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
        (* Process he *)
        /\ req_h = NullReq
        /\ sender_h = NullNode
        /\ pendingInvos_h = {}
        /\ now_h = timeOracle
        /\ allObjs = Objects
        (* Process ta *)
        /\ req_t = NullReq
        /\ sender_t = NullNode
        /\ pendingInvos_t = {}
        /\ now_t = timeOracle
        (* Process n *)
        /\ req = [self \in Nodes \ {head, tail, newTail} |-> NullReq]
        /\ sender = [self \in Nodes \ {head, tail, newTail} |-> NullNode]
        /\ now = [self \in Nodes \ {head, tail, newTail} |-> timeOracle]
        /\ pendingInvos = [self \in Nodes \ {head, tail, newTail} |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self = "initClient" -> "neverstart"
                                        [] self \in nonInitClients -> "waitForInit"
                                        [] self = "zookeeper" -> "listen_z"
                                        [] self = "head" -> "listen_h"
                                        [] self = "tail" -> "listen_t"
                                        [] self \in Nodes \ {head, tail, newTail} -> "tempCrash"]

neverstart == /\ pc["initClient"] = "neverstart"
              /\ FALSE
              /\ pc' = [pc EXCEPT !["initClient"] = "initializeObj"]
              /\ UNCHANGED << msgQs, objLogs, allSubmittedWriteOps, 
                              allSubmittedReadOps, terminatedYet, 
                              nonInitClients, start, timeOracle, Successors, 
                              Predecessors, uninitializedObjs, initObj, 
                              objs_init, obj_init, actions_init, action_init, 
                              gateway_cinit, msg_cinit, uniqueId_cinit, 
                              sentOps_init, recvdOps_init, objs, obj, actions, 
                              action, gateway_c, msg_c, uniqueId, sentOps, 
                              recvdOps, crashedNode, liveNode, req_z, 
                              liveNodes, req_h, sender_h, pendingInvos_h, 
                              now_h, allObjs, req_t, sender_t, pendingInvos_t, 
                              now_t, req, sender, now, pendingInvos >>

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
                 /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                                 allSubmittedReadOps, terminatedYet, 
                                 nonInitClients, timeOracle, Successors, 
                                 Predecessors, objs_init, obj_init, 
                                 actions_init, action_init, gateway_cinit, 
                                 msg_cinit, sentOps_init, recvdOps_init, objs, 
                                 obj, actions, action, gateway_c, msg_c, 
                                 uniqueId, sentOps, recvdOps, crashedNode, 
                                 liveNode, req_z, liveNodes, req_h, sender_h, 
                                 pendingInvos_h, now_h, allObjs, req_t, 
                                 sender_t, pendingInvos_t, now_t, req, sender, 
                                 now, pendingInvos >>

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
                /\ UNCHANGED << objLogs, terminatedYet, nonInitClients, start, 
                                timeOracle, Successors, Predecessors, 
                                uninitializedObjs, initObj, objs_init, 
                                obj_init, actions_init, action_init, 
                                gateway_cinit, uniqueId_cinit, sentOps_init, 
                                recvdOps_init, objs, obj, actions, action, 
                                gateway_c, msg_c, uniqueId, sentOps, recvdOps, 
                                crashedNode, liveNode, req_z, liveNodes, req_h, 
                                sender_h, pendingInvos_h, now_h, allObjs, 
                                req_t, sender_t, pendingInvos_t, now_t, req, 
                                sender, now, pendingInvos >>

concurrentOps_init == /\ pc["initClient"] = "concurrentOps_init"
                      /\ IF objs_init /= {}
                            THEN /\ obj_init' = (CHOOSE o \in objs_init: TRUE)
                                 /\ objs_init' = objs_init \ {obj_init'}
                                 /\ actions_init' = {WRITE_INV, READ_INV}
                                 /\ pc' = [pc EXCEPT !["initClient"] = "readOrWrite_init"]
                            ELSE /\ pc' = [pc EXCEPT !["initClient"] = "terminate_init"]
                                 /\ UNCHANGED << objs_init, obj_init, 
                                                 actions_init >>
                      /\ UNCHANGED << msgQs, objLogs, allSubmittedWriteOps, 
                                      allSubmittedReadOps, terminatedYet, 
                                      nonInitClients, start, timeOracle, 
                                      Successors, Predecessors, 
                                      uninitializedObjs, initObj, action_init, 
                                      gateway_cinit, msg_cinit, uniqueId_cinit, 
                                      sentOps_init, recvdOps_init, objs, obj, 
                                      actions, action, gateway_c, msg_c, 
                                      uniqueId, sentOps, recvdOps, crashedNode, 
                                      liveNode, req_z, liveNodes, req_h, 
                                      sender_h, pendingInvos_h, now_h, allObjs, 
                                      req_t, sender_t, pendingInvos_t, now_t, 
                                      req, sender, now, pendingInvos >>

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
                    /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                                    allSubmittedReadOps, terminatedYet, 
                                    nonInitClients, start, timeOracle, 
                                    Successors, Predecessors, 
                                    uninitializedObjs, initObj, objs_init, 
                                    obj_init, gateway_cinit, msg_cinit, 
                                    recvdOps_init, objs, obj, actions, action, 
                                    gateway_c, msg_c, uniqueId, sentOps, 
                                    recvdOps, crashedNode, liveNode, req_z, 
                                    liveNodes, req_h, sender_h, pendingInvos_h, 
                                    now_h, allObjs, req_t, sender_t, 
                                    pendingInvos_t, now_t, req, sender, now, 
                                    pendingInvos >>

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
                   /\ UNCHANGED << objLogs, terminatedYet, nonInitClients, 
                                   start, timeOracle, Successors, Predecessors, 
                                   uninitializedObjs, initObj, objs_init, 
                                   obj_init, actions_init, action_init, 
                                   uniqueId_cinit, sentOps_init, objs, obj, 
                                   actions, action, gateway_c, msg_c, uniqueId, 
                                   sentOps, recvdOps, crashedNode, liveNode, 
                                   req_z, liveNodes, req_h, sender_h, 
                                   pendingInvos_h, now_h, allObjs, req_t, 
                                   sender_t, pendingInvos_t, now_t, req, 
                                   sender, now, pendingInvos >>

terminate_init == /\ pc["initClient"] = "terminate_init"
                  /\ terminatedYet' = [terminatedYet EXCEPT ![initClient] = TRUE]
                  /\ pc' = [pc EXCEPT !["initClient"] = "Done"]
                  /\ UNCHANGED << msgQs, objLogs, allSubmittedWriteOps, 
                                  allSubmittedReadOps, nonInitClients, start, 
                                  timeOracle, Successors, Predecessors, 
                                  uninitializedObjs, initObj, objs_init, 
                                  obj_init, actions_init, action_init, 
                                  gateway_cinit, msg_cinit, uniqueId_cinit, 
                                  sentOps_init, recvdOps_init, objs, obj, 
                                  actions, action, gateway_c, msg_c, uniqueId, 
                                  sentOps, recvdOps, crashedNode, liveNode, 
                                  req_z, liveNodes, req_h, sender_h, 
                                  pendingInvos_h, now_h, allObjs, req_t, 
                                  sender_t, pendingInvos_t, now_t, req, sender, 
                                  now, pendingInvos >>

iclient == neverstart \/ initializeObj \/ waitFor_init
              \/ concurrentOps_init \/ readOrWrite_init \/ waitForOps_init
              \/ terminate_init

waitForInit(self) == /\ pc[self] = "waitForInit"
                     /\ start = TRUE
                     /\ pc' = [pc EXCEPT ![self] = "concurrentOps"]
                     /\ UNCHANGED << msgQs, objLogs, allSubmittedWriteOps, 
                                     allSubmittedReadOps, terminatedYet, 
                                     nonInitClients, start, timeOracle, 
                                     Successors, Predecessors, 
                                     uninitializedObjs, initObj, objs_init, 
                                     obj_init, actions_init, action_init, 
                                     gateway_cinit, msg_cinit, uniqueId_cinit, 
                                     sentOps_init, recvdOps_init, objs, obj, 
                                     actions, action, gateway_c, msg_c, 
                                     uniqueId, sentOps, recvdOps, crashedNode, 
                                     liveNode, req_z, liveNodes, req_h, 
                                     sender_h, pendingInvos_h, now_h, allObjs, 
                                     req_t, sender_t, pendingInvos_t, now_t, 
                                     req, sender, now, pendingInvos >>

concurrentOps(self) == /\ pc[self] = "concurrentOps"
                       /\ IF objs[self] /= {}
                             THEN /\ obj' = [obj EXCEPT ![self] = CHOOSE o \in objs[self]: TRUE]
                                  /\ objs' = [objs EXCEPT ![self] = objs[self] \ {obj'[self]}]
                                  /\ pc' = [pc EXCEPT ![self] = "readOrWrite"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "terminate"]
                                  /\ UNCHANGED << objs, obj >>
                       /\ UNCHANGED << msgQs, objLogs, allSubmittedWriteOps, 
                                       allSubmittedReadOps, terminatedYet, 
                                       nonInitClients, start, timeOracle, 
                                       Successors, Predecessors, 
                                       uninitializedObjs, initObj, objs_init, 
                                       obj_init, actions_init, action_init, 
                                       gateway_cinit, msg_cinit, 
                                       uniqueId_cinit, sentOps_init, 
                                       recvdOps_init, actions, action, 
                                       gateway_c, msg_c, uniqueId, sentOps, 
                                       recvdOps, crashedNode, liveNode, req_z, 
                                       liveNodes, req_h, sender_h, 
                                       pendingInvos_h, now_h, allObjs, req_t, 
                                       sender_t, pendingInvos_t, now_t, req, 
                                       sender, now, pendingInvos >>

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
                     /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                                     allSubmittedReadOps, terminatedYet, 
                                     nonInitClients, start, timeOracle, 
                                     Successors, Predecessors, 
                                     uninitializedObjs, initObj, objs_init, 
                                     obj_init, actions_init, action_init, 
                                     gateway_cinit, msg_cinit, uniqueId_cinit, 
                                     sentOps_init, recvdOps_init, objs, obj, 
                                     gateway_c, msg_c, recvdOps, crashedNode, 
                                     liveNode, req_z, liveNodes, req_h, 
                                     sender_h, pendingInvos_h, now_h, allObjs, 
                                     req_t, sender_t, pendingInvos_t, now_t, 
                                     req, sender, now, pendingInvos >>

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
                                         "Failure of assertion at line 315, column 21.")
                               /\ recvdOps' = [recvdOps EXCEPT ![self] = recvdOps[self] + 1]
                               /\ pc' = [pc EXCEPT ![self] = "waitForOps"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "readOrWrite"]
                               /\ UNCHANGED << msgQs, allSubmittedWriteOps, 
                                               allSubmittedReadOps, gateway_c, 
                                               msg_c, recvdOps >>
                    /\ UNCHANGED << objLogs, terminatedYet, nonInitClients, 
                                    start, timeOracle, Successors, 
                                    Predecessors, uninitializedObjs, initObj, 
                                    objs_init, obj_init, actions_init, 
                                    action_init, gateway_cinit, msg_cinit, 
                                    uniqueId_cinit, sentOps_init, 
                                    recvdOps_init, objs, obj, actions, action, 
                                    uniqueId, sentOps, crashedNode, liveNode, 
                                    req_z, liveNodes, req_h, sender_h, 
                                    pendingInvos_h, now_h, allObjs, req_t, 
                                    sender_t, pendingInvos_t, now_t, req, 
                                    sender, now, pendingInvos >>

terminate(self) == /\ pc[self] = "terminate"
                   /\ terminatedYet' = [terminatedYet EXCEPT ![self] = TRUE]
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << msgQs, objLogs, allSubmittedWriteOps, 
                                   allSubmittedReadOps, nonInitClients, start, 
                                   timeOracle, Successors, Predecessors, 
                                   uninitializedObjs, initObj, objs_init, 
                                   obj_init, actions_init, action_init, 
                                   gateway_cinit, msg_cinit, uniqueId_cinit, 
                                   sentOps_init, recvdOps_init, objs, obj, 
                                   actions, action, gateway_c, msg_c, uniqueId, 
                                   sentOps, recvdOps, crashedNode, liveNode, 
                                   req_z, liveNodes, req_h, sender_h, 
                                   pendingInvos_h, now_h, allObjs, req_t, 
                                   sender_t, pendingInvos_t, now_t, req, 
                                   sender, now, pendingInvos >>

c(self) == waitForInit(self) \/ concurrentOps(self) \/ readOrWrite(self)
              \/ waitForOps(self) \/ terminate(self)

listen_z == /\ pc["zookeeper"] = "listen_z"
            /\ \E temp \in {s \in SendersTo(Zookeeper): msgQs[<<s, Zookeeper>>] /= << >>}:
                 crashedNode' = temp
            /\ msgQs[<<crashedNode', Zookeeper>>] /= << >>
            /\ req_z' = Head(msgQs[<<crashedNode', Zookeeper>>])
            /\ msgQs' = [msgQs EXCEPT ![<<crashedNode', Zookeeper>>] = Tail(@)]
            /\ IF req_z'.callType = CRASHED
                  THEN /\ pc' = [pc EXCEPT !["zookeeper"] = "triggerWatches"]
                  ELSE /\ pc' = [pc EXCEPT !["zookeeper"] = "listen_z"]
            /\ UNCHANGED << objLogs, allSubmittedWriteOps, allSubmittedReadOps, 
                            terminatedYet, nonInitClients, start, timeOracle, 
                            Successors, Predecessors, uninitializedObjs, 
                            initObj, objs_init, obj_init, actions_init, 
                            action_init, gateway_cinit, msg_cinit, 
                            uniqueId_cinit, sentOps_init, recvdOps_init, objs, 
                            obj, actions, action, gateway_c, msg_c, uniqueId, 
                            sentOps, recvdOps, liveNode, liveNodes, req_h, 
                            sender_h, pendingInvos_h, now_h, allObjs, req_t, 
                            sender_t, pendingInvos_t, now_t, req, sender, now, 
                            pendingInvos >>

triggerWatches == /\ pc["zookeeper"] = "triggerWatches"
                  /\ IF liveNodes /= {crashedNode}
                        THEN /\ liveNode' = (CHOOSE ln \in liveNodes: ln /= crashedNode)
                             /\ msgQs' = [msgQs EXCEPT ![<<Zookeeper, liveNode'>>] = Append(@, ([ callType    |-> NODE_DEL,
                                                                                                  crashedNode  |-> crashedNode]))]
                             /\ liveNodes' = liveNodes \ {liveNode'}
                             /\ pc' = [pc EXCEPT !["zookeeper"] = "triggerWatches"]
                        ELSE /\ pc' = [pc EXCEPT !["zookeeper"] = "listen_z"]
                             /\ UNCHANGED << msgQs, liveNode, liveNodes >>
                  /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                                  allSubmittedReadOps, terminatedYet, 
                                  nonInitClients, start, timeOracle, 
                                  Successors, Predecessors, uninitializedObjs, 
                                  initObj, objs_init, obj_init, actions_init, 
                                  action_init, gateway_cinit, msg_cinit, 
                                  uniqueId_cinit, sentOps_init, recvdOps_init, 
                                  objs, obj, actions, action, gateway_c, msg_c, 
                                  uniqueId, sentOps, recvdOps, crashedNode, 
                                  req_z, req_h, sender_h, pendingInvos_h, 
                                  now_h, allObjs, req_t, sender_t, 
                                  pendingInvos_t, now_t, req, sender, now, 
                                  pendingInvos >>

zk == listen_z \/ triggerWatches

listen_h == /\ pc["head"] = "listen_h"
            /\ \E temp \in {s \in SendersTo(head): msgQs[<<s, head>>] /= << >>}:
                 sender_h' = temp
            /\ msgQs[<<sender_h', head>>] /= << >>
            /\ req_h' = Head(msgQs[<<sender_h', head>>])
            /\ msgQs' = [msgQs EXCEPT ![<<sender_h', head>>] = Tail(@)]
            /\ IF req_h'.callType = READ_INV
                  THEN /\ IF IsDirty(head, req_h'.op.obj)
                             THEN /\ pc' = [pc EXCEPT !["head"] = "apportionQ_h"]
                                  /\ UNCHANGED << timeOracle, now_h >>
                             ELSE /\ now_h' = timeOracle
                                  /\ timeOracle' = timeOracle + 1
                                  /\ pc' = [pc EXCEPT !["head"] = "respFromHead"]
                       /\ UNCHANGED << objLogs, Successors >>
                  ELSE /\ IF req_h'.callType = READ_RESP
                             THEN /\ pc' = [pc EXCEPT !["head"] = "readResp_h"]
                                  /\ UNCHANGED << objLogs, timeOracle, 
                                                  Successors, now_h >>
                             ELSE /\ IF req_h'.callType = WRITE_INV
                                        THEN /\ now_h' = timeOracle
                                             /\ timeOracle' = timeOracle + 1
                                             /\ pc' = [pc EXCEPT !["head"] = "dirtyWrite_h"]
                                             /\ UNCHANGED << objLogs, 
                                                             Successors >>
                                        ELSE /\ IF req_h'.callType = WRITE_RESP
                                                   THEN /\ objLogs' = [objLogs EXCEPT ![head][req_h'.op.obj] = CommitDirtyVersion(@, req_h'.op)]
                                                        /\ pc' = [pc EXCEPT !["head"] = "respToClient"]
                                                        /\ UNCHANGED Successors
                                                   ELSE /\ IF req_h'.callType = NODE_DEL
                                                              THEN /\ IF req_h'.crashedNode = Successors[head]
                                                                         THEN /\ Successors' = [Successors EXCEPT ![head] = Successors[Successors[head]]]
                                                                         ELSE /\ TRUE
                                                                              /\ UNCHANGED Successors
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED Successors
                                                        /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
                                                        /\ UNCHANGED objLogs
                                             /\ UNCHANGED << timeOracle, now_h >>
            /\ UNCHANGED << allSubmittedWriteOps, allSubmittedReadOps, 
                            terminatedYet, nonInitClients, start, Predecessors, 
                            uninitializedObjs, initObj, objs_init, obj_init, 
                            actions_init, action_init, gateway_cinit, 
                            msg_cinit, uniqueId_cinit, sentOps_init, 
                            recvdOps_init, objs, obj, actions, action, 
                            gateway_c, msg_c, uniqueId, sentOps, recvdOps, 
                            crashedNode, liveNode, req_z, liveNodes, 
                            pendingInvos_h, allObjs, req_t, sender_t, 
                            pendingInvos_t, now_t, req, sender, now, 
                            pendingInvos >>

apportionQ_h == /\ pc["head"] = "apportionQ_h"
                /\ msgQs' = [msgQs EXCEPT ![<<head, tail>>] = Append(@, req_h)]
                /\ pendingInvos_h' = (pendingInvos_h \cup {<<(req_h.uniqueId), sender_h>>})
                /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
                /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                                allSubmittedReadOps, terminatedYet, 
                                nonInitClients, start, timeOracle, Successors, 
                                Predecessors, uninitializedObjs, initObj, 
                                objs_init, obj_init, actions_init, action_init, 
                                gateway_cinit, msg_cinit, uniqueId_cinit, 
                                sentOps_init, recvdOps_init, objs, obj, 
                                actions, action, gateway_c, msg_c, uniqueId, 
                                sentOps, recvdOps, crashedNode, liveNode, 
                                req_z, liveNodes, req_h, sender_h, now_h, 
                                allObjs, req_t, sender_t, pendingInvos_t, 
                                now_t, req, sender, now, pendingInvos >>

respFromHead == /\ pc["head"] = "respFromHead"
                /\ req_h' = [ callType |-> READ_RESP,
                             uniqueId |-> req_h.uniqueId,
                             startTs |-> timeOracle,
                             commitTs |-> timeOracle,
                             op |-> Read(head, req_h.op.obj)]
                /\ msgQs' = [msgQs EXCEPT ![<<head, sender_h>>] = Append(@, req_h')]
                /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
                /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                                allSubmittedReadOps, terminatedYet, 
                                nonInitClients, start, timeOracle, Successors, 
                                Predecessors, uninitializedObjs, initObj, 
                                objs_init, obj_init, actions_init, action_init, 
                                gateway_cinit, msg_cinit, uniqueId_cinit, 
                                sentOps_init, recvdOps_init, objs, obj, 
                                actions, action, gateway_c, msg_c, uniqueId, 
                                sentOps, recvdOps, crashedNode, liveNode, 
                                req_z, liveNodes, sender_h, pendingInvos_h, 
                                now_h, allObjs, req_t, sender_t, 
                                pendingInvos_t, now_t, req, sender, now, 
                                pendingInvos >>

readResp_h == /\ pc["head"] = "readResp_h"
              /\ msgQs' = [msgQs EXCEPT ![<<head, (Find(pendingInvos_h, req_h.uniqueId))>>] = Append(@, req_h)]
              /\ pendingInvos_h' = pendingInvos_h \ {FindPair(pendingInvos_h, (req_h.uniqueId))}
              /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
              /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                              allSubmittedReadOps, terminatedYet, 
                              nonInitClients, start, timeOracle, Successors, 
                              Predecessors, uninitializedObjs, initObj, 
                              objs_init, obj_init, actions_init, action_init, 
                              gateway_cinit, msg_cinit, uniqueId_cinit, 
                              sentOps_init, recvdOps_init, objs, obj, actions, 
                              action, gateway_c, msg_c, uniqueId, sentOps, 
                              recvdOps, crashedNode, liveNode, req_z, 
                              liveNodes, req_h, sender_h, now_h, allObjs, 
                              req_t, sender_t, pendingInvos_t, now_t, req, 
                              sender, now, pendingInvos >>

dirtyWrite_h == /\ pc["head"] = "dirtyWrite_h"
                /\ req_h' = [req_h EXCEPT    !.startTs = now_h,
                                             !.op.writeStartTs = now_h,
                                             !.op.commitStatus = DIRTY]
                /\ objLogs' = [objLogs EXCEPT ![head][(req_h'.op).obj] = Cons((req_h'.op), @)]
                /\ msgQs' = [msgQs EXCEPT ![<<head, (Successors[head])>>] = Append(@, req_h')]
                /\ pendingInvos_h' = (pendingInvos_h \cup {<<(req_h'.uniqueId), sender_h>>})
                /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
                /\ UNCHANGED << allSubmittedWriteOps, allSubmittedReadOps, 
                                terminatedYet, nonInitClients, start, 
                                timeOracle, Successors, Predecessors, 
                                uninitializedObjs, initObj, objs_init, 
                                obj_init, actions_init, action_init, 
                                gateway_cinit, msg_cinit, uniqueId_cinit, 
                                sentOps_init, recvdOps_init, objs, obj, 
                                actions, action, gateway_c, msg_c, uniqueId, 
                                sentOps, recvdOps, crashedNode, liveNode, 
                                req_z, liveNodes, sender_h, now_h, allObjs, 
                                req_t, sender_t, pendingInvos_t, now_t, req, 
                                sender, now, pendingInvos >>

respToClient == /\ pc["head"] = "respToClient"
                /\ msgQs' = [msgQs EXCEPT ![<<head, (Find(pendingInvos_h, req_h.uniqueId))>>] = Append(@, req_h)]
                /\ pendingInvos_h' = pendingInvos_h \ {FindPair(pendingInvos_h, (req_h.uniqueId))}
                /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
                /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                                allSubmittedReadOps, terminatedYet, 
                                nonInitClients, start, timeOracle, Successors, 
                                Predecessors, uninitializedObjs, initObj, 
                                objs_init, obj_init, actions_init, action_init, 
                                gateway_cinit, msg_cinit, uniqueId_cinit, 
                                sentOps_init, recvdOps_init, objs, obj, 
                                actions, action, gateway_c, msg_c, uniqueId, 
                                sentOps, recvdOps, crashedNode, liveNode, 
                                req_z, liveNodes, req_h, sender_h, now_h, 
                                allObjs, req_t, sender_t, pendingInvos_t, 
                                now_t, req, sender, now, pendingInvos >>

he == listen_h \/ apportionQ_h \/ respFromHead \/ readResp_h
         \/ dirtyWrite_h \/ respToClient

listen_t == /\ pc["tail"] = "listen_t"
            /\ \E temp \in {s \in SendersTo(tail) : msgQs[<<s, tail>>] /= << >>}:
                 sender_t' = temp
            /\ msgQs[<<sender_t', tail>>] /= << >>
            /\ req_t' = Head(msgQs[<<sender_t', tail>>])
            /\ msgQs' = [msgQs EXCEPT ![<<sender_t', tail>>] = Tail(@)]
            /\ IF req_t'.callType = READ_INV
                  THEN /\ now_t' = timeOracle
                       /\ timeOracle' = timeOracle + 1
                       /\ pc' = [pc EXCEPT !["tail"] = "respFromSelf_t"]
                       /\ UNCHANGED << objLogs, Predecessors >>
                  ELSE /\ IF req_t'.callType = WRITE_INV
                             THEN /\ now_t' = timeOracle
                                  /\ timeOracle' = timeOracle + 1
                                  /\ objLogs' = [objLogs EXCEPT ![tail][([req_t'.op EXCEPT    !.writeCommitTs = now_t',
                                                                                              !.commitStatus = CLEAN]).obj] = Cons(([req_t'.op EXCEPT    !.writeCommitTs = now_t',
                                                                                                                                                         !.commitStatus = CLEAN]), @)]
                                  /\ pc' = [pc EXCEPT !["tail"] = "tailAck"]
                                  /\ UNCHANGED Predecessors
                             ELSE /\ IF req_t'.callType = NODE_DEL
                                        THEN /\ IF req_t'.crashedNode = Predecessors[tail]
                                                   THEN /\ Predecessors' = [Predecessors EXCEPT ![tail] = Predecessors[Predecessors[tail]]]
                                                        /\ pc' = [pc EXCEPT !["tail"] = "rolenode"]
                                                   ELSE /\ pc' = [pc EXCEPT !["tail"] = "listen_t"]
                                                        /\ UNCHANGED Predecessors
                                        ELSE /\ pc' = [pc EXCEPT !["tail"] = "listen_t"]
                                             /\ UNCHANGED Predecessors
                                  /\ UNCHANGED << objLogs, timeOracle, now_t >>
            /\ UNCHANGED << allSubmittedWriteOps, allSubmittedReadOps, 
                            terminatedYet, nonInitClients, start, Successors, 
                            uninitializedObjs, initObj, objs_init, obj_init, 
                            actions_init, action_init, gateway_cinit, 
                            msg_cinit, uniqueId_cinit, sentOps_init, 
                            recvdOps_init, objs, obj, actions, action, 
                            gateway_c, msg_c, uniqueId, sentOps, recvdOps, 
                            crashedNode, liveNode, req_z, liveNodes, req_h, 
                            sender_h, pendingInvos_h, now_h, allObjs, 
                            pendingInvos_t, req, sender, now, pendingInvos >>

respFromSelf_t == /\ pc["tail"] = "respFromSelf_t"
                  /\ req_t' =  [ callType |-> READ_RESP,
                              uniqueId |-> req_t.uniqueId,
                              startTs |-> now_t,
                              commitTs |-> now_t,
                              op |-> Read(tail, req_t.op.obj)]
                  /\ msgQs' = [msgQs EXCEPT ![<<tail, sender_t>>] = Append(@, req_t')]
                  /\ pc' = [pc EXCEPT !["tail"] = "listen_t"]
                  /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                                  allSubmittedReadOps, terminatedYet, 
                                  nonInitClients, start, timeOracle, 
                                  Successors, Predecessors, uninitializedObjs, 
                                  initObj, objs_init, obj_init, actions_init, 
                                  action_init, gateway_cinit, msg_cinit, 
                                  uniqueId_cinit, sentOps_init, recvdOps_init, 
                                  objs, obj, actions, action, gateway_c, msg_c, 
                                  uniqueId, sentOps, recvdOps, crashedNode, 
                                  liveNode, req_z, liveNodes, req_h, sender_h, 
                                  pendingInvos_h, now_h, allObjs, sender_t, 
                                  pendingInvos_t, now_t, req, sender, now, 
                                  pendingInvos >>

tailAck == /\ pc["tail"] = "tailAck"
           /\ req_t' = [ callType |-> WRITE_RESP,
                         uniqueId |-> req_t.uniqueId,
                         startTs |-> req_t.startTs,
                         commitTs |-> Read(tail, req_t.op.obj).writeCommitTs,
                         op |-> Read(tail, req_t.op.obj)]
           /\ msgQs' = [msgQs EXCEPT ![<<tail, (Predecessors[tail])>>] = Append(@, req_t')]
           /\ pc' = [pc EXCEPT !["tail"] = "listen_t"]
           /\ UNCHANGED << objLogs, allSubmittedWriteOps, allSubmittedReadOps, 
                           terminatedYet, nonInitClients, start, timeOracle, 
                           Successors, Predecessors, uninitializedObjs, 
                           initObj, objs_init, obj_init, actions_init, 
                           action_init, gateway_cinit, msg_cinit, 
                           uniqueId_cinit, sentOps_init, recvdOps_init, objs, 
                           obj, actions, action, gateway_c, msg_c, uniqueId, 
                           sentOps, recvdOps, crashedNode, liveNode, req_z, 
                           liveNodes, req_h, sender_h, pendingInvos_h, now_h, 
                           allObjs, sender_t, pendingInvos_t, now_t, req, 
                           sender, now, pendingInvos >>

rolenode == /\ pc["tail"] = "rolenode"
            /\ \E temp \in {s \in SendersTo(tail) : msgQs[<<s, tail>>] /= << >>}:
                 sender' = [sender EXCEPT !["tail"] = temp]
            /\ msgQs[<<sender'["tail"], tail>>] /= << >>
            /\ req' = [req EXCEPT !["tail"] = Head(msgQs[<<sender'["tail"], tail>>])]
            /\ msgQs' = [msgQs EXCEPT ![<<sender'["tail"], tail>>] = Tail(@)]
            /\ IF req'["tail"].callType = READ_INV
                  THEN /\ IF IsDirty(tail, req'["tail"].op.obj)
                             THEN /\ pc' = [pc EXCEPT !["tail"] = "apportionQ_"]
                                  /\ UNCHANGED << timeOracle, now >>
                             ELSE /\ now' = [now EXCEPT !["tail"] = timeOracle]
                                  /\ timeOracle' = timeOracle + 1
                                  /\ pc' = [pc EXCEPT !["tail"] = "respFromSelf_"]
                       /\ UNCHANGED objLogs
                  ELSE /\ IF req'["tail"].callType = READ_RESP
                             THEN /\ pc' = [pc EXCEPT !["tail"] = "fwdFromTail_"]
                                  /\ UNCHANGED objLogs
                             ELSE /\ IF req'["tail"].callType = WRITE_INV
                                        THEN /\ objLogs' = [objLogs EXCEPT ![tail][(req'["tail"].op).obj] = Cons((req'["tail"].op), @)]
                                             /\ pc' = [pc EXCEPT !["tail"] = "propagate_"]
                                        ELSE /\ objLogs' = [objLogs EXCEPT ![tail][req'["tail"].op.obj] = CommitDirtyVersion(@, req'["tail"].op)]
                                             /\ pc' = [pc EXCEPT !["tail"] = "backProp_"]
                       /\ UNCHANGED << timeOracle, now >>
            /\ UNCHANGED << allSubmittedWriteOps, allSubmittedReadOps, 
                            terminatedYet, nonInitClients, start, Successors, 
                            Predecessors, uninitializedObjs, initObj, 
                            objs_init, obj_init, actions_init, action_init, 
                            gateway_cinit, msg_cinit, uniqueId_cinit, 
                            sentOps_init, recvdOps_init, objs, obj, actions, 
                            action, gateway_c, msg_c, uniqueId, sentOps, 
                            recvdOps, crashedNode, liveNode, req_z, liveNodes, 
                            req_h, sender_h, pendingInvos_h, now_h, allObjs, 
                            req_t, sender_t, pendingInvos_t, now_t, 
                            pendingInvos >>

apportionQ_ == /\ pc["tail"] = "apportionQ_"
               /\ msgQs' = [msgQs EXCEPT ![<<tail, newTail>>] = Append(@, req["tail"])]
               /\ pendingInvos' = [pendingInvos EXCEPT !["tail"] = pendingInvos["tail"] \cup {<<(req["tail"].uniqueId), sender["tail"]>>}]
               /\ pc' = [pc EXCEPT !["tail"] = "rolenode"]
               /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                               allSubmittedReadOps, terminatedYet, 
                               nonInitClients, start, timeOracle, Successors, 
                               Predecessors, uninitializedObjs, initObj, 
                               objs_init, obj_init, actions_init, action_init, 
                               gateway_cinit, msg_cinit, uniqueId_cinit, 
                               sentOps_init, recvdOps_init, objs, obj, actions, 
                               action, gateway_c, msg_c, uniqueId, sentOps, 
                               recvdOps, crashedNode, liveNode, req_z, 
                               liveNodes, req_h, sender_h, pendingInvos_h, 
                               now_h, allObjs, req_t, sender_t, pendingInvos_t, 
                               now_t, req, sender, now >>

respFromSelf_ == /\ pc["tail"] = "respFromSelf_"
                 /\ req' = [req EXCEPT !["tail"] =   [callType |-> READ_RESP,
                                                   uniqueId |-> req["tail"].uniqueId,
                                                   startTs |-> now["tail"],
                                                   commitTs |-> now["tail"],
                                                   op |-> Read(tail, req["tail"].op.obj)]]
                 /\ msgQs' = [msgQs EXCEPT ![<<tail, sender["tail"]>>] = Append(@, req'["tail"])]
                 /\ pc' = [pc EXCEPT !["tail"] = "rolenode"]
                 /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                                 allSubmittedReadOps, terminatedYet, 
                                 nonInitClients, start, timeOracle, Successors, 
                                 Predecessors, uninitializedObjs, initObj, 
                                 objs_init, obj_init, actions_init, 
                                 action_init, gateway_cinit, msg_cinit, 
                                 uniqueId_cinit, sentOps_init, recvdOps_init, 
                                 objs, obj, actions, action, gateway_c, msg_c, 
                                 uniqueId, sentOps, recvdOps, crashedNode, 
                                 liveNode, req_z, liveNodes, req_h, sender_h, 
                                 pendingInvos_h, now_h, allObjs, req_t, 
                                 sender_t, pendingInvos_t, now_t, sender, now, 
                                 pendingInvos >>

fwdFromTail_ == /\ pc["tail"] = "fwdFromTail_"
                /\ msgQs' = [msgQs EXCEPT ![<<tail, (Find(pendingInvos["tail"], req["tail"].uniqueId))>>] = Append(@, req["tail"])]
                /\ pendingInvos' = [pendingInvos EXCEPT !["tail"] = pendingInvos["tail"] \ {FindPair(pendingInvos["tail"], (req["tail"].uniqueId))}]
                /\ pc' = [pc EXCEPT !["tail"] = "rolenode"]
                /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                                allSubmittedReadOps, terminatedYet, 
                                nonInitClients, start, timeOracle, Successors, 
                                Predecessors, uninitializedObjs, initObj, 
                                objs_init, obj_init, actions_init, action_init, 
                                gateway_cinit, msg_cinit, uniqueId_cinit, 
                                sentOps_init, recvdOps_init, objs, obj, 
                                actions, action, gateway_c, msg_c, uniqueId, 
                                sentOps, recvdOps, crashedNode, liveNode, 
                                req_z, liveNodes, req_h, sender_h, 
                                pendingInvos_h, now_h, allObjs, req_t, 
                                sender_t, pendingInvos_t, now_t, req, sender, 
                                now >>

propagate_ == /\ pc["tail"] = "propagate_"
              /\ msgQs' = [msgQs EXCEPT ![<<tail, (Successors[tail])>>] = Append(@, req["tail"])]
              /\ pendingInvos' = [pendingInvos EXCEPT !["tail"] = pendingInvos["tail"] \cup {<<(req["tail"].uniqueId), sender["tail"]>>}]
              /\ pc' = [pc EXCEPT !["tail"] = "rolenode"]
              /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                              allSubmittedReadOps, terminatedYet, 
                              nonInitClients, start, timeOracle, Successors, 
                              Predecessors, uninitializedObjs, initObj, 
                              objs_init, obj_init, actions_init, action_init, 
                              gateway_cinit, msg_cinit, uniqueId_cinit, 
                              sentOps_init, recvdOps_init, objs, obj, actions, 
                              action, gateway_c, msg_c, uniqueId, sentOps, 
                              recvdOps, crashedNode, liveNode, req_z, 
                              liveNodes, req_h, sender_h, pendingInvos_h, 
                              now_h, allObjs, req_t, sender_t, pendingInvos_t, 
                              now_t, req, sender, now >>

backProp_ == /\ pc["tail"] = "backProp_"
             /\ msgQs' = [msgQs EXCEPT ![<<tail, (Find(pendingInvos["tail"], req["tail"].uniqueId))>>] = Append(@, req["tail"])]
             /\ pendingInvos' = [pendingInvos EXCEPT !["tail"] = pendingInvos["tail"] \ {FindPair(pendingInvos["tail"], (req["tail"].uniqueId))}]
             /\ pc' = [pc EXCEPT !["tail"] = "rolenode"]
             /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                             allSubmittedReadOps, terminatedYet, 
                             nonInitClients, start, timeOracle, Successors, 
                             Predecessors, uninitializedObjs, initObj, 
                             objs_init, obj_init, actions_init, action_init, 
                             gateway_cinit, msg_cinit, uniqueId_cinit, 
                             sentOps_init, recvdOps_init, objs, obj, actions, 
                             action, gateway_c, msg_c, uniqueId, sentOps, 
                             recvdOps, crashedNode, liveNode, req_z, liveNodes, 
                             req_h, sender_h, pendingInvos_h, now_h, allObjs, 
                             req_t, sender_t, pendingInvos_t, now_t, req, 
                             sender, now >>

ta == listen_t \/ respFromSelf_t \/ tailAck \/ rolenode \/ apportionQ_
         \/ respFromSelf_ \/ fwdFromTail_ \/ propagate_ \/ backProp_

tempCrash(self) == /\ pc[self] = "tempCrash"
                   /\ pc' = [pc EXCEPT ![self] = "crash"]
                   /\ UNCHANGED << msgQs, objLogs, allSubmittedWriteOps, 
                                   allSubmittedReadOps, terminatedYet, 
                                   nonInitClients, start, timeOracle, 
                                   Successors, Predecessors, uninitializedObjs, 
                                   initObj, objs_init, obj_init, actions_init, 
                                   action_init, gateway_cinit, msg_cinit, 
                                   uniqueId_cinit, sentOps_init, recvdOps_init, 
                                   objs, obj, actions, action, gateway_c, 
                                   msg_c, uniqueId, sentOps, recvdOps, 
                                   crashedNode, liveNode, req_z, liveNodes, 
                                   req_h, sender_h, pendingInvos_h, now_h, 
                                   allObjs, req_t, sender_t, pendingInvos_t, 
                                   now_t, req, sender, now, pendingInvos >>

listen(self) == /\ pc[self] = "listen"
                /\ \E temp \in {s \in SendersTo(self) : msgQs[<<s, self>>] /= << >>}:
                     sender' = [sender EXCEPT ![self] = temp]
                /\ msgQs[<<sender'[self], self>>] /= << >>
                /\ req' = [req EXCEPT ![self] = Head(msgQs[<<sender'[self], self>>])]
                /\ msgQs' = [msgQs EXCEPT ![<<sender'[self], self>>] = Tail(@)]
                /\ IF req'[self].callType = READ_INV
                      THEN /\ IF IsDirty(self, req'[self].op.obj)
                                 THEN /\ IF IsCrashed(self)
                                            THEN /\ pc' = [pc EXCEPT ![self] = "crash"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "apportionQ"]
                                      /\ UNCHANGED << timeOracle, now >>
                                 ELSE /\ now' = [now EXCEPT ![self] = timeOracle]
                                      /\ timeOracle' = timeOracle + 1
                                      /\ pc' = [pc EXCEPT ![self] = "respFromSelf"]
                           /\ UNCHANGED objLogs
                      ELSE /\ IF req'[self].callType = READ_RESP
                                 THEN /\ IF IsCrashed(self)
                                            THEN /\ pc' = [pc EXCEPT ![self] = "crash"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "fwdFromTail"]
                                      /\ UNCHANGED objLogs
                                 ELSE /\ IF req'[self].callType = WRITE_INV
                                            THEN /\ objLogs' = [objLogs EXCEPT ![self][(req'[self].op).obj] = Cons((req'[self].op), @)]
                                                 /\ IF IsCrashed(self)
                                                       THEN /\ pc' = [pc EXCEPT ![self] = "crash"]
                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "propagate"]
                                            ELSE /\ objLogs' = [objLogs EXCEPT ![self][req'[self].op.obj] = CommitDirtyVersion(@, req'[self].op)]
                                                 /\ IF IsCrashed(self)
                                                       THEN /\ pc' = [pc EXCEPT ![self] = "crash"]
                                                       ELSE /\ pc' = [pc EXCEPT ![self] = "backProp"]
                           /\ UNCHANGED << timeOracle, now >>
                /\ UNCHANGED << allSubmittedWriteOps, allSubmittedReadOps, 
                                terminatedYet, nonInitClients, start, 
                                Successors, Predecessors, uninitializedObjs, 
                                initObj, objs_init, obj_init, actions_init, 
                                action_init, gateway_cinit, msg_cinit, 
                                uniqueId_cinit, sentOps_init, recvdOps_init, 
                                objs, obj, actions, action, gateway_c, msg_c, 
                                uniqueId, sentOps, recvdOps, crashedNode, 
                                liveNode, req_z, liveNodes, req_h, sender_h, 
                                pendingInvos_h, now_h, allObjs, req_t, 
                                sender_t, pendingInvos_t, now_t, pendingInvos >>

apportionQ(self) == /\ pc[self] = "apportionQ"
                    /\ msgQs' = [msgQs EXCEPT ![<<self, tail>>] = Append(@, req[self])]
                    /\ IF IsCrashed(self)
                          THEN /\ pc' = [pc EXCEPT ![self] = "crash"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "crashLabel"]
                    /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                                    allSubmittedReadOps, terminatedYet, 
                                    nonInitClients, start, timeOracle, 
                                    Successors, Predecessors, 
                                    uninitializedObjs, initObj, objs_init, 
                                    obj_init, actions_init, action_init, 
                                    gateway_cinit, msg_cinit, uniqueId_cinit, 
                                    sentOps_init, recvdOps_init, objs, obj, 
                                    actions, action, gateway_c, msg_c, 
                                    uniqueId, sentOps, recvdOps, crashedNode, 
                                    liveNode, req_z, liveNodes, req_h, 
                                    sender_h, pendingInvos_h, now_h, allObjs, 
                                    req_t, sender_t, pendingInvos_t, now_t, 
                                    req, sender, now, pendingInvos >>

crashLabel(self) == /\ pc[self] = "crashLabel"
                    /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \cup {<<(req[self].uniqueId), sender[self]>>}]
                    /\ pc' = [pc EXCEPT ![self] = "listen"]
                    /\ UNCHANGED << msgQs, objLogs, allSubmittedWriteOps, 
                                    allSubmittedReadOps, terminatedYet, 
                                    nonInitClients, start, timeOracle, 
                                    Successors, Predecessors, 
                                    uninitializedObjs, initObj, objs_init, 
                                    obj_init, actions_init, action_init, 
                                    gateway_cinit, msg_cinit, uniqueId_cinit, 
                                    sentOps_init, recvdOps_init, objs, obj, 
                                    actions, action, gateway_c, msg_c, 
                                    uniqueId, sentOps, recvdOps, crashedNode, 
                                    liveNode, req_z, liveNodes, req_h, 
                                    sender_h, pendingInvos_h, now_h, allObjs, 
                                    req_t, sender_t, pendingInvos_t, now_t, 
                                    req, sender, now >>

respFromSelf(self) == /\ pc[self] = "respFromSelf"
                      /\ req' = [req EXCEPT ![self] =   [callType |-> READ_RESP,
                                                      uniqueId |-> req[self].uniqueId,
                                                      startTs |-> now[self],
                                                      commitTs |-> now[self],
                                                      op |-> Read(self, req[self].op.obj)]]
                      /\ IF IsCrashed(self)
                            THEN /\ pc' = [pc EXCEPT ![self] = "crash"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "sendLabel"]
                      /\ UNCHANGED << msgQs, objLogs, allSubmittedWriteOps, 
                                      allSubmittedReadOps, terminatedYet, 
                                      nonInitClients, start, timeOracle, 
                                      Successors, Predecessors, 
                                      uninitializedObjs, initObj, objs_init, 
                                      obj_init, actions_init, action_init, 
                                      gateway_cinit, msg_cinit, uniqueId_cinit, 
                                      sentOps_init, recvdOps_init, objs, obj, 
                                      actions, action, gateway_c, msg_c, 
                                      uniqueId, sentOps, recvdOps, crashedNode, 
                                      liveNode, req_z, liveNodes, req_h, 
                                      sender_h, pendingInvos_h, now_h, allObjs, 
                                      req_t, sender_t, pendingInvos_t, now_t, 
                                      sender, now, pendingInvos >>

sendLabel(self) == /\ pc[self] = "sendLabel"
                   /\ msgQs' = [msgQs EXCEPT ![<<self, sender[self]>>] = Append(@, req[self])]
                   /\ IF IsCrashed(self)
                         THEN /\ pc' = [pc EXCEPT ![self] = "crash"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "listen"]
                   /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                                   allSubmittedReadOps, terminatedYet, 
                                   nonInitClients, start, timeOracle, 
                                   Successors, Predecessors, uninitializedObjs, 
                                   initObj, objs_init, obj_init, actions_init, 
                                   action_init, gateway_cinit, msg_cinit, 
                                   uniqueId_cinit, sentOps_init, recvdOps_init, 
                                   objs, obj, actions, action, gateway_c, 
                                   msg_c, uniqueId, sentOps, recvdOps, 
                                   crashedNode, liveNode, req_z, liveNodes, 
                                   req_h, sender_h, pendingInvos_h, now_h, 
                                   allObjs, req_t, sender_t, pendingInvos_t, 
                                   now_t, req, sender, now, pendingInvos >>

fwdFromTail(self) == /\ pc[self] = "fwdFromTail"
                     /\ msgQs' = [msgQs EXCEPT ![<<self, (Find(pendingInvos[self], req[self].uniqueId))>>] = Append(@, req[self])]
                     /\ pc' = [pc EXCEPT ![self] = "crashLabelReadResp"]
                     /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                                     allSubmittedReadOps, terminatedYet, 
                                     nonInitClients, start, timeOracle, 
                                     Successors, Predecessors, 
                                     uninitializedObjs, initObj, objs_init, 
                                     obj_init, actions_init, action_init, 
                                     gateway_cinit, msg_cinit, uniqueId_cinit, 
                                     sentOps_init, recvdOps_init, objs, obj, 
                                     actions, action, gateway_c, msg_c, 
                                     uniqueId, sentOps, recvdOps, crashedNode, 
                                     liveNode, req_z, liveNodes, req_h, 
                                     sender_h, pendingInvos_h, now_h, allObjs, 
                                     req_t, sender_t, pendingInvos_t, now_t, 
                                     req, sender, now, pendingInvos >>

crashLabelReadResp(self) == /\ pc[self] = "crashLabelReadResp"
                            /\ IF IsCrashed(self)
                                  THEN /\ pc' = [pc EXCEPT ![self] = "crash"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "removeLabel"]
                            /\ UNCHANGED << msgQs, objLogs, 
                                            allSubmittedWriteOps, 
                                            allSubmittedReadOps, terminatedYet, 
                                            nonInitClients, start, timeOracle, 
                                            Successors, Predecessors, 
                                            uninitializedObjs, initObj, 
                                            objs_init, obj_init, actions_init, 
                                            action_init, gateway_cinit, 
                                            msg_cinit, uniqueId_cinit, 
                                            sentOps_init, recvdOps_init, objs, 
                                            obj, actions, action, gateway_c, 
                                            msg_c, uniqueId, sentOps, recvdOps, 
                                            crashedNode, liveNode, req_z, 
                                            liveNodes, req_h, sender_h, 
                                            pendingInvos_h, now_h, allObjs, 
                                            req_t, sender_t, pendingInvos_t, 
                                            now_t, req, sender, now, 
                                            pendingInvos >>

removeLabel(self) == /\ pc[self] = "removeLabel"
                     /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \ {FindPair(pendingInvos[self], (req[self].uniqueId))}]
                     /\ pc' = [pc EXCEPT ![self] = "listen"]
                     /\ UNCHANGED << msgQs, objLogs, allSubmittedWriteOps, 
                                     allSubmittedReadOps, terminatedYet, 
                                     nonInitClients, start, timeOracle, 
                                     Successors, Predecessors, 
                                     uninitializedObjs, initObj, objs_init, 
                                     obj_init, actions_init, action_init, 
                                     gateway_cinit, msg_cinit, uniqueId_cinit, 
                                     sentOps_init, recvdOps_init, objs, obj, 
                                     actions, action, gateway_c, msg_c, 
                                     uniqueId, sentOps, recvdOps, crashedNode, 
                                     liveNode, req_z, liveNodes, req_h, 
                                     sender_h, pendingInvos_h, now_h, allObjs, 
                                     req_t, sender_t, pendingInvos_t, now_t, 
                                     req, sender, now >>

propagate(self) == /\ pc[self] = "propagate"
                   /\ msgQs' = [msgQs EXCEPT ![<<self, (Successors[self])>>] = Append(@, req[self])]
                   /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \cup {<<(req[self].uniqueId), sender[self]>>}]
                   /\ pc' = [pc EXCEPT ![self] = "crashLabelWriteInv"]
                   /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                                   allSubmittedReadOps, terminatedYet, 
                                   nonInitClients, start, timeOracle, 
                                   Successors, Predecessors, uninitializedObjs, 
                                   initObj, objs_init, obj_init, actions_init, 
                                   action_init, gateway_cinit, msg_cinit, 
                                   uniqueId_cinit, sentOps_init, recvdOps_init, 
                                   objs, obj, actions, action, gateway_c, 
                                   msg_c, uniqueId, sentOps, recvdOps, 
                                   crashedNode, liveNode, req_z, liveNodes, 
                                   req_h, sender_h, pendingInvos_h, now_h, 
                                   allObjs, req_t, sender_t, pendingInvos_t, 
                                   now_t, req, sender, now >>

crashLabelWriteInv(self) == /\ pc[self] = "crashLabelWriteInv"
                            /\ IF IsCrashed(self)
                                  THEN /\ pc' = [pc EXCEPT ![self] = "crash"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "listen"]
                            /\ UNCHANGED << msgQs, objLogs, 
                                            allSubmittedWriteOps, 
                                            allSubmittedReadOps, terminatedYet, 
                                            nonInitClients, start, timeOracle, 
                                            Successors, Predecessors, 
                                            uninitializedObjs, initObj, 
                                            objs_init, obj_init, actions_init, 
                                            action_init, gateway_cinit, 
                                            msg_cinit, uniqueId_cinit, 
                                            sentOps_init, recvdOps_init, objs, 
                                            obj, actions, action, gateway_c, 
                                            msg_c, uniqueId, sentOps, recvdOps, 
                                            crashedNode, liveNode, req_z, 
                                            liveNodes, req_h, sender_h, 
                                            pendingInvos_h, now_h, allObjs, 
                                            req_t, sender_t, pendingInvos_t, 
                                            now_t, req, sender, now, 
                                            pendingInvos >>

backProp(self) == /\ pc[self] = "backProp"
                  /\ msgQs' = [msgQs EXCEPT ![<<self, (Find(pendingInvos[self], req[self].uniqueId))>>] = Append(@, req[self])]
                  /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \ {FindPair(pendingInvos[self], (req[self].uniqueId))}]
                  /\ pc' = [pc EXCEPT ![self] = "crashLabelWriteResp"]
                  /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                                  allSubmittedReadOps, terminatedYet, 
                                  nonInitClients, start, timeOracle, 
                                  Successors, Predecessors, uninitializedObjs, 
                                  initObj, objs_init, obj_init, actions_init, 
                                  action_init, gateway_cinit, msg_cinit, 
                                  uniqueId_cinit, sentOps_init, recvdOps_init, 
                                  objs, obj, actions, action, gateway_c, msg_c, 
                                  uniqueId, sentOps, recvdOps, crashedNode, 
                                  liveNode, req_z, liveNodes, req_h, sender_h, 
                                  pendingInvos_h, now_h, allObjs, req_t, 
                                  sender_t, pendingInvos_t, now_t, req, sender, 
                                  now >>

crashLabelWriteResp(self) == /\ pc[self] = "crashLabelWriteResp"
                             /\ IF IsCrashed(self)
                                   THEN /\ pc' = [pc EXCEPT ![self] = "crash"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "listen"]
                             /\ UNCHANGED << msgQs, objLogs, 
                                             allSubmittedWriteOps, 
                                             allSubmittedReadOps, 
                                             terminatedYet, nonInitClients, 
                                             start, timeOracle, Successors, 
                                             Predecessors, uninitializedObjs, 
                                             initObj, objs_init, obj_init, 
                                             actions_init, action_init, 
                                             gateway_cinit, msg_cinit, 
                                             uniqueId_cinit, sentOps_init, 
                                             recvdOps_init, objs, obj, actions, 
                                             action, gateway_c, msg_c, 
                                             uniqueId, sentOps, recvdOps, 
                                             crashedNode, liveNode, req_z, 
                                             liveNodes, req_h, sender_h, 
                                             pendingInvos_h, now_h, allObjs, 
                                             req_t, sender_t, pendingInvos_t, 
                                             now_t, req, sender, now, 
                                             pendingInvos >>

crash(self) == /\ pc[self] = "crash"
               /\ msgQs' = [msgQs EXCEPT ![<<self, Zookeeper>>] = Append(@, ([ callType |-> CRASHED ]))]
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                               allSubmittedReadOps, terminatedYet, 
                               nonInitClients, start, timeOracle, Successors, 
                               Predecessors, uninitializedObjs, initObj, 
                               objs_init, obj_init, actions_init, action_init, 
                               gateway_cinit, msg_cinit, uniqueId_cinit, 
                               sentOps_init, recvdOps_init, objs, obj, actions, 
                               action, gateway_c, msg_c, uniqueId, sentOps, 
                               recvdOps, crashedNode, liveNode, req_z, 
                               liveNodes, req_h, sender_h, pendingInvos_h, 
                               now_h, allObjs, req_t, sender_t, pendingInvos_t, 
                               now_t, req, sender, now, pendingInvos >>

n(self) == tempCrash(self) \/ listen(self) \/ apportionQ(self)
              \/ crashLabel(self) \/ respFromSelf(self) \/ sendLabel(self)
              \/ fwdFromTail(self) \/ crashLabelReadResp(self)
              \/ removeLabel(self) \/ propagate(self)
              \/ crashLabelWriteInv(self) \/ backProp(self)
              \/ crashLabelWriteResp(self) \/ crash(self)

Next == iclient \/ zk \/ he \/ ta
           \/ (\E self \in nonInitClients: c(self))
           \/ (\E self \in Nodes \ {head, tail, newTail}: n(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ WF_vars(iclient)
        /\ \A self \in nonInitClients : WF_vars(c(self))
        /\ WF_vars(zk)
        /\ WF_vars(he)
        /\ WF_vars(ta)
        /\ \A self \in Nodes \ {head, tail, newTail} : WF_vars(n(self))

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
                        
HeadTypeInvariant ==    /\ req_h \in RequestType \cup {NullReq}
                        /\ sender_h \in Nodes \cup Clients \cup {NullNode}
\*                        /\ pendingInvos_h \in thisoneshard
                        /\ now_h \in Nat
                        
TailTypeInvariant ==    /\ req_t \in RequestType \cup {NullReq}
                        /\ sender_t \in Nodes \cup Clients \cup {NullNode}
\*                        /\ pendingInvos_t \in thisoneshard
                        /\ now_t \in Nat

    
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
\* Last modified Sat Jul 29 20:53:58 EDT 2023 by 72jen
\* Last modified Fri Jun 23 20:02:52 EDT 2023 by jenniferlam
\* Created Tue Jun 13 12:56:59 EDT 2023 by jenniferlam
