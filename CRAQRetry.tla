----------------------------- MODULE CRAQRetry -----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Clients, Nodes, head, tail, NumWrites, NumReads, Objects, MaxTimestamp

NumMsgs == NumWrites + NumReads

RECURSIVE FormChainTopology(_,_)
FormChainTopology(curr, nodes) ==   IF nodes = {} THEN {} 
                                    ELSE LET n == CHOOSE node \in nodes : TRUE
                                         IN  {<<curr, n>>} \cup FormChainTopology(n, nodes \ {n})
                                            
NextEdges == FormChainTopology(head, Nodes \ {head})
PrevEdges == { <<e[2], e[1]>> : e \in NextEdges } 

Successors == [n \in Nodes \ {tail} |-> LET e == CHOOSE edge \in NextEdges : edge[1] = n IN e[2]]
Predecessors == [n \in Nodes \ {head} |-> LET e == CHOOSE edge \in PrevEdges : edge[1] = n IN e[2]]

EdgesToTail == { <<n, tail>> : n \in Nodes \ {tail}}
EdgesFromTail == { <<tail, n>> : n \in Nodes \ {tail}}
Edges == NextEdges \cup PrevEdges \cup EdgesToTail \cup EdgesFromTail

EdgesFromClients == { <<c, n>> : c \in Clients, n \in Nodes}
EdgesToClients == { <<n, c>> : c \in Clients, n \in Nodes }
ClientEdges == EdgesFromClients \cup EdgesToClients

Network == Edges \cup ClientEdges

UniqueIdType == {<<c, id>> : c \in Clients, id \in 0..NumMsgs}
NullUniqueId == CHOOSE id : id \notin UniqueIdType
SendersTo(n) == {edge[1]: edge \in {e \in Network: e[2] = n}}

ASSUME  /\ head \in Nodes
        /\ tail \in Nodes
        /\ Cardinality(Nodes) >= 2
        /\ Cardinality(Edges) = Cardinality(Nodes \ {head}) * 2 + Cardinality(Nodes \ {tail}) * 2 - 2
        /\ Edges \subseteq Network
        /\ ClientEdges \subseteq Network
        /\ Cardinality(UniqueIdType) = Cardinality(Clients) * (NumMsgs + 1)
        
-----------------------------------------------------------------------------
\* CallType
READ_INV == "READ_INV" \* Read invocation
WRITE_INV == "WRITE_INV" \* Write invocation
READ_RESP == "READ_RESP" \* Read response
WRITE_RESP == "WRITE_RESP" \* Write response

\* CommitType
CLEAN == "CLEAN"
DIRTY == "DIRTY"


NullNode == CHOOSE n : n \notin Nodes
NullObj == CHOOSE o \in Objects: TRUE


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
                objTotalOrders = [ o \in Objects |-> << >> ],
                allSubmittedOps = [o \in Objects |-> {}],
                terminatedYet = [c \in Clients |-> FALSE],
                initClient = CHOOSE c \in Clients: TRUE,
                nonInitClients = Clients \ {initClient},
                start = FALSE,
                timeOracle = 10;
                
    \* operator definitions
    define {
        
        RECURSIVE CommitDirtyVersion(_, _) 
        CommitDirtyVersion(objLog, committedVer) == LET mostRecentVer == Head(objLog)
                                                        uniqueId == committedVer.uniqueId
                                                        writeCommitTs == committedVer.writeCommitTs IN 
                                                    IF mostRecentVer.uniqueId = uniqueId THEN
                                                        Cons([mostRecentVer EXCEPT !.commitStatus = CLEAN,
                                                                                    !.writeCommitTs = writeCommitTs], 
                                                                Tail(objLog))
                                                    ELSE
                                                        Cons(mostRecentVer, 
                                                                CommitDirtyVersion(Tail(objLog), committedVer))
        
        IsDirty(node, obj) == Head(objLogs[node][obj]).commitStatus = DIRTY        
        Read(node, obj) == Head(objLogs[node][obj])
        FindPair(set, k) == CHOOSE kv \in set: kv[1] = k
        Find(set, k) == LET kv == FindPair(set, k) IN kv[2]
        
        Increment(id) == <<id[1], id[2]+1>>
        
    }
    
    \* macro definitions
    macro send(sender, receiver, msg) {
        msgQs[<<sender, receiver>>] := Append(@, msg)
    }
    
    macro recv(sender, receiver, msg) {
\*        when msgQs[<<sender, receiver>>] /= << >>;
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
        allSubmittedOps[reqOp.op.obj] := allSubmittedOps[reqOp.op.obj] \cup {reqOp};
    }
    
\*    
\*    fair process(time="timeOracle") {
\*        oracle: 
\*        while (TRUE) {
\*            timeOracle := timeOracle + 1;
\*        }
\*    }

    fair process(iclient = "initClient")
        variables   uninitializedObjs = Objects,
                    initObj = NullObj,
                    objs_init = Objects,
                    obj_init = NullObj,
                    actions_init = {WRITE_INV, READ_INV},
                    action_init = NullCall,
                    gateway_cinit = NullNode,
                    i_init = 1,
                    msg_cinit = NullReq,
                    uniqueId_cinit = <<initClient, 1>>;
    {
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
            
            waitForInit:
            when msgQs[<<head, initClient>>] /= << >>; 
            recv(head, initClient, msg_cinit); 
            addToOpSet(msg_cinit);
        };
        start := TRUE;
        
        concurrentOps_init: while (objs_init /= {}) {
            obj_init := CHOOSE o \in objs_init: TRUE;
            objs_init := objs_init \ {obj_init};
            
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
            } 
            
        };
        
        waitForOps_init:
        while (i_init <= Cardinality(Objects) * 2) {
            i_init := i_init + 1;
            with (temp \in {s \in SendersTo(initClient): msgQs[<<s, initClient>>] /= << >>}) {
                gateway_cinit := temp;
            };
            recv(gateway_cinit, initClient, msg_cinit);
            addToOpSet(msg_cinit); 
        };
        
        terminatedYet[initClient] := TRUE
    }
    
    fair process(c \in nonInitClients)
        variables   objs = Objects,
                    obj = NullObj,
                    actions = {WRITE_INV, READ_INV},
                    action = NullCall,
                    gateway_c = NullNode,
                    i = 1,
                    msg_c = NullReq,
                    uniqueId = <<initClient, 1>>;
    {   
        waitForInit: when start = TRUE;
        concurrentOps: while (objs /= {}) {
            obj := CHOOSE o \in objs: TRUE;
            objs := objs \ {obj};
            
            readOrWrite: while (actions /= {}) {
                action := CHOOSE a \in actions: TRUE;
                actions := actions \ {action};
                
                send(   initClient, 
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
            } 
            
        };
        
        waitForOps:
        while (i <= Cardinality(Objects) * 2) {
            i := i + 1;
            with (temp \in {s \in SendersTo(initClient): msgQs[<<s, initClient>>] /= << >>}) {
                gateway_c := temp;
            };
            recv(gateway_c, initClient, msg_c); 
            addToOpSet(msg_c);
        };
        
        terminatedYet[self] := TRUE;
    }
    
\*    fair process(c \in Clients)
\*        variables   uniqueId = <<self, 1>>,
\*                    msg = NullReq,
\*                    gateway = NullNode;
\*    {
\*        clientWrite: 
\*        send(self, head, [  callType |-> WRITE_INV,
\*                            uniqueId |-> uniqueId,
\*                            startTs |-> NullTs,
\*                            commitTs |-> NullTs,
\*                            op |-> [obj |-> CHOOSE o \in Objects: TRUE,
\*                                    uniqueId |-> uniqueId,
\*                                    writeStartTs |-> NullTs,
\*                                    writeCommitTs |-> NullTs,
\*                                    commitStatus |-> NullCommitStatus]]);
\*                                    
\*        recvdWriteResp: with (temp \in {s \in SendersTo(self): msgQs[<<s, self>>] /= << >>}) {
\*            gateway := temp;
\*        };
\*        recv(gateway, self, msg); 
\*        assert(msg.uniqueId = uniqueId);
\*        assert(msg.callType = WRITE_RESP);
\*        addToOpSet(msg);
\*        
\*        clientReadToTail:
\*        uniqueId := <<self, 2>>;
\*        send(self, tail, [  callType |-> READ_INV,
\*                            uniqueId |-> uniqueId,
\*                            startTs |-> NullTs,
\*                            commitTs |-> NullTs,
\*                            op |-> [    obj |-> CHOOSE o \in Objects : TRUE,
\*                                        uniqueId |-> NullUniqueId,
\*                                        writeStartTs |-> NullTs,
\*                                        writeCommitTs |-> NullTs,
\*                                        commitStatus |-> NullCommitStatus]]);
\*                                        
\*        recvdReadResp: with (temp \in {node \in SendersTo(self) : msgQs[node, self] /= << >>}) {
\*            gateway := temp;
\*        }; 
\*        recv(gateway, self, msg);
\*        assert(msg.uniqueId = uniqueId);
\*        assert(msg.callType = READ_RESP);
\*        addToOpSet(msg);
\*
\*        clientReadToHead:
\*        uniqueId := <<self, 3>>;
\*        send(self, head, [  callType |-> READ_INV,
\*                            uniqueId |-> uniqueId,
\*                            startTs |-> NullTs,
\*                            commitTs |-> NullTs,
\*                            op |-> [    obj |-> CHOOSE o \in Objects : TRUE,
\*                                        uniqueId |-> NullUniqueId,
\*                                        writeStartTs |-> NullTs,
\*                                        writeCommitTs |-> NullTs,
\*                                        commitStatus |-> NullCommitStatus]]);
\*                                        
\*        recvdReadRespFromHead: 
\*        with (temp \in {node \in SendersTo(self) : msgQs[node, self] /= << >>}) {
\*            gateway := temp;
\*        }; 
\*        recv(gateway, self, msg);
\*        assert(msg.uniqueId = uniqueId);
\*        assert(msg.callType = READ_RESP);
\*        addToOpSet(msg);
\*        
\*        concurrentWrite:
\*        uniqueId := <<self, 4>>;
\*        send(self, head, [  callType |-> WRITE_INV,
\*                            uniqueId |-> uniqueId,
\*                            startTs |-> NullTs,
\*                            commitTs |-> NullTs,
\*                            op |-> [obj |-> CHOOSE o \in Objects: TRUE,
\*                                    uniqueId |-> uniqueId,
\*                                    writeStartTs |-> NullTs,
\*                                    writeCommitTs |-> NullTs,
\*                                    commitStatus |-> NullCommitStatus]]);
\*        
\*        concurrentReadToNode:                            
\*        send(self, CHOOSE n \in Nodes: n \notin {head, tail}, [  callType |-> READ_INV,
\*                            uniqueId |-> <<self, 5>>,
\*                            startTs |-> NullTs,
\*                            commitTs |-> NullTs,
\*                            op |-> [    obj |-> CHOOSE o \in Objects: TRUE,
\*                                        uniqueId |-> NullUniqueId,
\*                                        writeStartTs |-> NullTs,
\*                                        writeCommitTs |-> NullTs,
\*                                        commitStatus |-> NullCommitStatus]]);
\*        concurrentReadToHead:
\*        send(self, head, [  callType |-> READ_INV,
\*                            uniqueId |-> <<self, 6>>,
\*                            startTs |-> NullTs,
\*                            commitTs |-> NullTs,
\*                            op |-> [    obj |-> CHOOSE o \in Objects: TRUE,
\*                                        uniqueId |-> NullUniqueId,
\*                                        writeStartTs |-> NullTs,
\*                                        writeCommitTs |-> NullTs,
\*                                        commitStatus |-> NullCommitStatus]]);        
\*        waitForConcurrentOp1:
\*        with (temp \in {node \in SendersTo(self) : msgQs[node, self] /= << >>}) {
\*            gateway := temp;
\*        };
\*        recv(gateway, self, msg);
\*        assert( \/(msg.callType = WRITE_RESP /\ msg.uniqueId = <<self, 4>>) 
\*                \/(msg.callType = READ_RESP /\ msg.uniqueId = <<self, 5>>)
\*                \/(msg.callType = READ_RESP /\ msg.uniqueId = <<self, 6>>));
\*        addToOpSet(msg);
\*        
\*        waitForConcurrentOp2:
\*        with (temp \in {node \in SendersTo(self) : msgQs[node, self] /= << >>}) {
\*            gateway := temp;
\*        };
\*        recv(gateway, self, msg);
\*        assert( \/(msg.callType = WRITE_RESP /\ msg.uniqueId = <<self, 4>>) 
\*                \/(msg.callType = READ_RESP /\ msg.uniqueId = <<self, 5>>)
\*                \/(msg.callType = READ_RESP /\ msg.uniqueId = <<self, 6>>));
\*        addToOpSet(msg);
\*        
\*        waitForConcurrentOp3:
\*        with (temp \in {node \in SendersTo(self) : msgQs[node, self] /= << >>}) {
\*            gateway := temp;
\*        };
\*        recv(gateway, self, msg);
\*        assert( \/(msg.callType = WRITE_RESP /\ msg.uniqueId = <<self, 4>>) 
\*                \/(msg.callType = READ_RESP /\ msg.uniqueId = <<self, 5>>)
\*                \/(msg.callType = READ_RESP /\ msg.uniqueId = <<self, 6>>));
\*        addToOpSet(msg);        
\*        
\*        terminatedYet[self] := TRUE;
\*    }
    
    fair process(he="head") 
        variables req_h = NullReq,
                  sender_h = NullNode,
                  pendingInvos_h = {},
                  now_h = timeOracle;
    {
        listen_h: while (TRUE) {
            with (temp \in {s \in SendersTo(head): msgQs[<<s, head>>] /= << >>}) {
                sender_h := temp;
            }; 
            
            incomingMsg_h: recv(sender_h, head, req_h);
            
            if (req_h.callType = READ_INV) {
                if (IsDirty(head, req_h.op.obj)) {
                    apportionQ_h: send(head, tail, req_h);
                    add(pendingInvos_h, req_h.uniqueId, sender_h);
                } else {
                    now_h := timeOracle;
                    timeOracle := timeOracle + 1;
                    addReadTO_h: req_h := [ callType |-> READ_RESP,
                                            uniqueId |-> req_h.uniqueId,
                                            startTs |-> timeOracle,
                                            commitTs |-> timeOracle,
                                            op |-> Read(head, req_h.op.obj)];
                    objTotalOrders[req_h.op.obj] := Cons(req_h, @);
                    respFromHead: send(head, sender_h, req_h);
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
                        propagate_h: send(head, Successors[head], req_h);
                        add(pendingInvos_h, req_h.uniqueId, sender_h);
                    } else { \* WRITE_RESP
                        objLogs[head][req_h.op.obj] := CommitDirtyVersion(@, req_h.op);
                        respToClient: send(head, Find(pendingInvos_h, req_h.uniqueId), req_h);
                        remove(pendingInvos_h, req_h.uniqueId);
                    }
                }
            }
        }
    }
    
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
            
            incomingMsg_t: recv(sender_t, tail, req_t);
            if (req_t.callType = READ_INV) {
                now_t := timeOracle;
                timeOracle := timeOracle + 1;
                addReadTO_t: req_t := [ callType |-> READ_RESP,
                                        uniqueId |-> req_t.uniqueId,
                                        startTs |-> now_t,
                                        commitTs |-> now_t,
                                        op |-> Read(tail, req_t.op.obj)];
                objTotalOrders[req_t.op.obj] := Cons(req_t, @);
                respFromSelf_t: send(tail, sender_t, req_t);
            } else { \* WRITE_INV
                now_t := timeOracle;
                timeOracle := timeOracle + 1;
                write(tail, [req_t.op EXCEPT  !.writeCommitTs = now_t, 
                                              !.commitStatus = CLEAN]);
                addWriteTO_t: req_t := [    callType |-> WRITE_RESP,
                                            uniqueId |-> req_t.uniqueId,
                                            startTs |-> req_t.startTs,
                                            commitTs |-> Read(tail, req_t.op.obj).writeCommitTs,
                                            op |-> Read(tail, req_t.op.obj)];
                objTotalOrders[req_t.op.obj] := Cons(req_t, @);
                tailAck: send(tail, Predecessors[tail], req_t);   
            }
        }
    }
    
    fair process(n \in Nodes \ {head, tail})
        variables   req = NullReq,
                    sender = NullNode,
                    now = timeOracle, 
                    pendingInvos = {};
    {
        listen: while (TRUE) {
            with (temp \in {s \in SendersTo(self) : msgQs[<<s, self>>] /= << >>}) {
                sender := temp;
            };
            
            incomingMsg: recv(sender, self, req); 
            
            if (req.callType = READ_INV) {
                if (IsDirty(self, req.op.obj)) {                 
                    apportionQ: send(self, tail, req);
                    add(pendingInvos, req.uniqueId, sender);
                } else {
                    now := timeOracle;
                    timeOracle := timeOracle + 1;
                    addReadTO: req :=  [callType |-> READ_RESP,
                                        uniqueId |-> req.uniqueId,
                                        startTs |-> now,
                                        commitTs |-> now,
                                        op |-> Read(self, req.op.obj)];
                    objTotalOrders[req.op.obj] := Cons(req, @);
                    respFromSelf: send(self, sender, req);
                } 
            } else {
                if (req.callType = READ_RESP) {
                    fwdFromTail: send(self, Find(pendingInvos, req.uniqueId), req);
                    remove(pendingInvos, req.uniqueId);
                } else { 
                    if (req.callType = WRITE_INV) {
                        write(self, req.op);
                        
                        propagate: send(self, Successors[self], req);
                        add(pendingInvos, req.uniqueId, sender)
                    } else { \* WRITE_RESP
                        
                        objLogs[self][req.op.obj] := CommitDirtyVersion(@, req.op);
                        
                        backProp: send(self, Find(pendingInvos, req.uniqueId), req);
                        remove(pendingInvos, req.uniqueId);
                    };
                }
            }  
        }
    }
}

****************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "c8cb4f7" /\ chksum(tla) = "63635c70")
\* Label waitForInit of process iclient at line 190 col 13 changed to waitForInit_
VARIABLES msgQs, objLogs, objTotalOrders, allSubmittedOps, terminatedYet, 
          initClient, nonInitClients, start, timeOracle, pc

(* define statement *)
RECURSIVE CommitDirtyVersion(_, _)
CommitDirtyVersion(objLog, committedVer) == LET mostRecentVer == Head(objLog)
                                                uniqueId == committedVer.uniqueId
                                                writeCommitTs == committedVer.writeCommitTs IN
                                            IF mostRecentVer.uniqueId = uniqueId THEN
                                                Cons([mostRecentVer EXCEPT !.commitStatus = CLEAN,
                                                                            !.writeCommitTs = writeCommitTs],
                                                        Tail(objLog))
                                            ELSE
                                                Cons(mostRecentVer,
                                                        CommitDirtyVersion(Tail(objLog), committedVer))

IsDirty(node, obj) == Head(objLogs[node][obj]).commitStatus = DIRTY
Read(node, obj) == Head(objLogs[node][obj])
FindPair(set, k) == CHOOSE kv \in set: kv[1] = k
Find(set, k) == LET kv == FindPair(set, k) IN kv[2]

Increment(id) == <<id[1], id[2]+1>>

VARIABLES uninitializedObjs, initObj, objs_init, obj_init, actions_init, 
          action_init, gateway_cinit, i_init, msg_cinit, uniqueId_cinit, objs, 
          obj, actions, action, gateway_c, i, msg_c, uniqueId, req_h, 
          sender_h, pendingInvos_h, now_h, req_t, sender_t, pendingInvos_t, 
          now_t, req, sender, now, pendingInvos

vars == << msgQs, objLogs, objTotalOrders, allSubmittedOps, terminatedYet, 
           initClient, nonInitClients, start, timeOracle, pc, 
           uninitializedObjs, initObj, objs_init, obj_init, actions_init, 
           action_init, gateway_cinit, i_init, msg_cinit, uniqueId_cinit, 
           objs, obj, actions, action, gateway_c, i, msg_c, uniqueId, req_h, 
           sender_h, pendingInvos_h, now_h, req_t, sender_t, pendingInvos_t, 
           now_t, req, sender, now, pendingInvos >>

ProcSet == {"initClient"} \cup (nonInitClients) \cup {"head"} \cup {"tail"} \cup (Nodes \ {head, tail})

Init == (* Global variables *)
        /\ msgQs = [edge \in Network |-> << >>]
        /\ objLogs = [n \in Nodes |-> [o \in Objects |-> << >>]]
        /\ objTotalOrders = [ o \in Objects |-> << >> ]
        /\ allSubmittedOps = [o \in Objects |-> {}]
        /\ terminatedYet = [c \in Clients |-> FALSE]
        /\ initClient = (CHOOSE c \in Clients: TRUE)
        /\ nonInitClients = Clients \ {initClient}
        /\ start = FALSE
        /\ timeOracle = 10
        (* Process iclient *)
        /\ uninitializedObjs = Objects
        /\ initObj = NullObj
        /\ objs_init = Objects
        /\ obj_init = NullObj
        /\ actions_init = {WRITE_INV, READ_INV}
        /\ action_init = NullCall
        /\ gateway_cinit = NullNode
        /\ i_init = 1
        /\ msg_cinit = NullReq
        /\ uniqueId_cinit = <<initClient, 1>>
        (* Process c *)
        /\ objs = [self \in nonInitClients |-> Objects]
        /\ obj = [self \in nonInitClients |-> NullObj]
        /\ actions = [self \in nonInitClients |-> {WRITE_INV, READ_INV}]
        /\ action = [self \in nonInitClients |-> NullCall]
        /\ gateway_c = [self \in nonInitClients |-> NullNode]
        /\ i = [self \in nonInitClients |-> 1]
        /\ msg_c = [self \in nonInitClients |-> NullReq]
        /\ uniqueId = [self \in nonInitClients |-> <<initClient, 1>>]
        (* Process he *)
        /\ req_h = NullReq
        /\ sender_h = NullNode
        /\ pendingInvos_h = {}
        /\ now_h = timeOracle
        (* Process ta *)
        /\ req_t = NullReq
        /\ sender_t = NullNode
        /\ pendingInvos_t = {}
        /\ now_t = timeOracle
        (* Process n *)
        /\ req = [self \in Nodes \ {head, tail} |-> NullReq]
        /\ sender = [self \in Nodes \ {head, tail} |-> NullNode]
        /\ now = [self \in Nodes \ {head, tail} |-> timeOracle]
        /\ pendingInvos = [self \in Nodes \ {head, tail} |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self = "initClient" -> "initializeObj"
                                        [] self \in nonInitClients -> "waitForInit"
                                        [] self = "head" -> "listen_h"
                                        [] self = "tail" -> "listen_t"
                                        [] self \in Nodes \ {head, tail} -> "listen"]

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
                            /\ pc' = [pc EXCEPT !["initClient"] = "waitForInit_"]
                            /\ start' = start
                       ELSE /\ start' = TRUE
                            /\ pc' = [pc EXCEPT !["initClient"] = "concurrentOps_init"]
                            /\ UNCHANGED << msgQs, uninitializedObjs, initObj, 
                                            uniqueId_cinit >>
                 /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                                 terminatedYet, initClient, nonInitClients, 
                                 timeOracle, objs_init, obj_init, actions_init, 
                                 action_init, gateway_cinit, i_init, msg_cinit, 
                                 objs, obj, actions, action, gateway_c, i, 
                                 msg_c, uniqueId, req_h, sender_h, 
                                 pendingInvos_h, now_h, req_t, sender_t, 
                                 pendingInvos_t, now_t, req, sender, now, 
                                 pendingInvos >>

waitForInit_ == /\ pc["initClient"] = "waitForInit_"
                /\ msgQs[<<head, initClient>>] /= << >>
                /\ msg_cinit' = Head(msgQs[<<head, initClient>>])
                /\ msgQs' = [msgQs EXCEPT ![<<head, initClient>>] = Tail(@)]
                /\ allSubmittedOps' = [allSubmittedOps EXCEPT ![msg_cinit'.op.obj] = allSubmittedOps[msg_cinit'.op.obj] \cup {msg_cinit'}]
                /\ pc' = [pc EXCEPT !["initClient"] = "initializeObj"]
                /\ UNCHANGED << objLogs, objTotalOrders, terminatedYet, 
                                initClient, nonInitClients, start, timeOracle, 
                                uninitializedObjs, initObj, objs_init, 
                                obj_init, actions_init, action_init, 
                                gateway_cinit, i_init, uniqueId_cinit, objs, 
                                obj, actions, action, gateway_c, i, msg_c, 
                                uniqueId, req_h, sender_h, pendingInvos_h, 
                                now_h, req_t, sender_t, pendingInvos_t, now_t, 
                                req, sender, now, pendingInvos >>

concurrentOps_init == /\ pc["initClient"] = "concurrentOps_init"
                      /\ IF objs_init /= {}
                            THEN /\ obj_init' = (CHOOSE o \in objs_init: TRUE)
                                 /\ objs_init' = objs_init \ {obj_init'}
                                 /\ pc' = [pc EXCEPT !["initClient"] = "readOrWrite_init"]
                            ELSE /\ pc' = [pc EXCEPT !["initClient"] = "waitForOps_init"]
                                 /\ UNCHANGED << objs_init, obj_init >>
                      /\ UNCHANGED << msgQs, objLogs, objTotalOrders, 
                                      allSubmittedOps, terminatedYet, 
                                      initClient, nonInitClients, start, 
                                      timeOracle, uninitializedObjs, initObj, 
                                      actions_init, action_init, gateway_cinit, 
                                      i_init, msg_cinit, uniqueId_cinit, objs, 
                                      obj, actions, action, gateway_c, i, 
                                      msg_c, uniqueId, req_h, sender_h, 
                                      pendingInvos_h, now_h, req_t, sender_t, 
                                      pendingInvos_t, now_t, req, sender, now, 
                                      pendingInvos >>

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
                               /\ pc' = [pc EXCEPT !["initClient"] = "readOrWrite_init"]
                          ELSE /\ pc' = [pc EXCEPT !["initClient"] = "concurrentOps_init"]
                               /\ UNCHANGED << msgQs, actions_init, 
                                               action_init, uniqueId_cinit >>
                    /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                                    terminatedYet, initClient, nonInitClients, 
                                    start, timeOracle, uninitializedObjs, 
                                    initObj, objs_init, obj_init, 
                                    gateway_cinit, i_init, msg_cinit, objs, 
                                    obj, actions, action, gateway_c, i, msg_c, 
                                    uniqueId, req_h, sender_h, pendingInvos_h, 
                                    now_h, req_t, sender_t, pendingInvos_t, 
                                    now_t, req, sender, now, pendingInvos >>

waitForOps_init == /\ pc["initClient"] = "waitForOps_init"
                   /\ IF i_init <= Cardinality(Objects) * 2
                         THEN /\ i_init' = i_init + 1
                              /\ \E temp \in {s \in SendersTo(initClient): msgQs[<<s, initClient>>] /= << >>}:
                                   gateway_cinit' = temp
                              /\ msg_cinit' = Head(msgQs[<<gateway_cinit', initClient>>])
                              /\ msgQs' = [msgQs EXCEPT ![<<gateway_cinit', initClient>>] = Tail(@)]
                              /\ allSubmittedOps' = [allSubmittedOps EXCEPT ![msg_cinit'.op.obj] = allSubmittedOps[msg_cinit'.op.obj] \cup {msg_cinit'}]
                              /\ pc' = [pc EXCEPT !["initClient"] = "waitForOps_init"]
                              /\ UNCHANGED terminatedYet
                         ELSE /\ terminatedYet' = [terminatedYet EXCEPT ![initClient] = TRUE]
                              /\ pc' = [pc EXCEPT !["initClient"] = "Done"]
                              /\ UNCHANGED << msgQs, allSubmittedOps, 
                                              gateway_cinit, i_init, msg_cinit >>
                   /\ UNCHANGED << objLogs, objTotalOrders, initClient, 
                                   nonInitClients, start, timeOracle, 
                                   uninitializedObjs, initObj, objs_init, 
                                   obj_init, actions_init, action_init, 
                                   uniqueId_cinit, objs, obj, actions, action, 
                                   gateway_c, i, msg_c, uniqueId, req_h, 
                                   sender_h, pendingInvos_h, now_h, req_t, 
                                   sender_t, pendingInvos_t, now_t, req, 
                                   sender, now, pendingInvos >>

iclient == initializeObj \/ waitForInit_ \/ concurrentOps_init
              \/ readOrWrite_init \/ waitForOps_init

waitForInit(self) == /\ pc[self] = "waitForInit"
                     /\ start = TRUE
                     /\ pc' = [pc EXCEPT ![self] = "concurrentOps"]
                     /\ UNCHANGED << msgQs, objLogs, objTotalOrders, 
                                     allSubmittedOps, terminatedYet, 
                                     initClient, nonInitClients, start, 
                                     timeOracle, uninitializedObjs, initObj, 
                                     objs_init, obj_init, actions_init, 
                                     action_init, gateway_cinit, i_init, 
                                     msg_cinit, uniqueId_cinit, objs, obj, 
                                     actions, action, gateway_c, i, msg_c, 
                                     uniqueId, req_h, sender_h, pendingInvos_h, 
                                     now_h, req_t, sender_t, pendingInvos_t, 
                                     now_t, req, sender, now, pendingInvos >>

concurrentOps(self) == /\ pc[self] = "concurrentOps"
                       /\ IF objs[self] /= {}
                             THEN /\ obj' = [obj EXCEPT ![self] = CHOOSE o \in objs[self]: TRUE]
                                  /\ objs' = [objs EXCEPT ![self] = objs[self] \ {obj'[self]}]
                                  /\ pc' = [pc EXCEPT ![self] = "readOrWrite"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "waitForOps"]
                                  /\ UNCHANGED << objs, obj >>
                       /\ UNCHANGED << msgQs, objLogs, objTotalOrders, 
                                       allSubmittedOps, terminatedYet, 
                                       initClient, nonInitClients, start, 
                                       timeOracle, uninitializedObjs, initObj, 
                                       objs_init, obj_init, actions_init, 
                                       action_init, gateway_cinit, i_init, 
                                       msg_cinit, uniqueId_cinit, actions, 
                                       action, gateway_c, i, msg_c, uniqueId, 
                                       req_h, sender_h, pendingInvos_h, now_h, 
                                       req_t, sender_t, pendingInvos_t, now_t, 
                                       req, sender, now, pendingInvos >>

readOrWrite(self) == /\ pc[self] = "readOrWrite"
                     /\ IF actions[self] /= {}
                           THEN /\ action' = [action EXCEPT ![self] = CHOOSE a \in actions[self]: TRUE]
                                /\ actions' = [actions EXCEPT ![self] = actions[self] \ {action'[self]}]
                                /\ msgQs' = [msgQs EXCEPT ![<<initClient, (IF action'[self] = WRITE_INV THEN head ELSE CHOOSE n \in Nodes: n /= head)>>] = Append(@, ([   callType |-> action'[self],
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
                                /\ pc' = [pc EXCEPT ![self] = "readOrWrite"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "concurrentOps"]
                                /\ UNCHANGED << msgQs, actions, action, 
                                                uniqueId >>
                     /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                                     terminatedYet, initClient, nonInitClients, 
                                     start, timeOracle, uninitializedObjs, 
                                     initObj, objs_init, obj_init, 
                                     actions_init, action_init, gateway_cinit, 
                                     i_init, msg_cinit, uniqueId_cinit, objs, 
                                     obj, gateway_c, i, msg_c, req_h, sender_h, 
                                     pendingInvos_h, now_h, req_t, sender_t, 
                                     pendingInvos_t, now_t, req, sender, now, 
                                     pendingInvos >>

waitForOps(self) == /\ pc[self] = "waitForOps"
                    /\ IF i[self] <= Cardinality(Objects) * 2
                          THEN /\ i' = [i EXCEPT ![self] = i[self] + 1]
                               /\ \E temp \in {s \in SendersTo(initClient): msgQs[<<s, initClient>>] /= << >>}:
                                    gateway_c' = [gateway_c EXCEPT ![self] = temp]
                               /\ msg_c' = [msg_c EXCEPT ![self] = Head(msgQs[<<gateway_c'[self], initClient>>])]
                               /\ msgQs' = [msgQs EXCEPT ![<<gateway_c'[self], initClient>>] = Tail(@)]
                               /\ allSubmittedOps' = [allSubmittedOps EXCEPT ![msg_c'[self].op.obj] = allSubmittedOps[msg_c'[self].op.obj] \cup {msg_c'[self]}]
                               /\ pc' = [pc EXCEPT ![self] = "waitForOps"]
                               /\ UNCHANGED terminatedYet
                          ELSE /\ terminatedYet' = [terminatedYet EXCEPT ![self] = TRUE]
                               /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << msgQs, allSubmittedOps, 
                                               gateway_c, i, msg_c >>
                    /\ UNCHANGED << objLogs, objTotalOrders, initClient, 
                                    nonInitClients, start, timeOracle, 
                                    uninitializedObjs, initObj, objs_init, 
                                    obj_init, actions_init, action_init, 
                                    gateway_cinit, i_init, msg_cinit, 
                                    uniqueId_cinit, objs, obj, actions, action, 
                                    uniqueId, req_h, sender_h, pendingInvos_h, 
                                    now_h, req_t, sender_t, pendingInvos_t, 
                                    now_t, req, sender, now, pendingInvos >>

c(self) == waitForInit(self) \/ concurrentOps(self) \/ readOrWrite(self)
              \/ waitForOps(self)

listen_h == /\ pc["head"] = "listen_h"
            /\ \E temp \in {s \in SendersTo(head): msgQs[<<s, head>>] /= << >>}:
                 sender_h' = temp
            /\ pc' = [pc EXCEPT !["head"] = "incomingMsg_h"]
            /\ UNCHANGED << msgQs, objLogs, objTotalOrders, allSubmittedOps, 
                            terminatedYet, initClient, nonInitClients, start, 
                            timeOracle, uninitializedObjs, initObj, objs_init, 
                            obj_init, actions_init, action_init, gateway_cinit, 
                            i_init, msg_cinit, uniqueId_cinit, objs, obj, 
                            actions, action, gateway_c, i, msg_c, uniqueId, 
                            req_h, pendingInvos_h, now_h, req_t, sender_t, 
                            pendingInvos_t, now_t, req, sender, now, 
                            pendingInvos >>

incomingMsg_h == /\ pc["head"] = "incomingMsg_h"
                 /\ req_h' = Head(msgQs[<<sender_h, head>>])
                 /\ msgQs' = [msgQs EXCEPT ![<<sender_h, head>>] = Tail(@)]
                 /\ IF req_h'.callType = READ_INV
                       THEN /\ IF IsDirty(head, req_h'.op.obj)
                                  THEN /\ pc' = [pc EXCEPT !["head"] = "apportionQ_h"]
                                       /\ UNCHANGED << timeOracle, now_h >>
                                  ELSE /\ now_h' = timeOracle
                                       /\ timeOracle' = timeOracle + 1
                                       /\ pc' = [pc EXCEPT !["head"] = "addReadTO_h"]
                            /\ UNCHANGED objLogs
                       ELSE /\ IF req_h'.callType = READ_RESP
                                  THEN /\ pc' = [pc EXCEPT !["head"] = "readResp_h"]
                                       /\ UNCHANGED << objLogs, timeOracle, 
                                                       now_h >>
                                  ELSE /\ IF req_h'.callType = WRITE_INV
                                             THEN /\ now_h' = timeOracle
                                                  /\ timeOracle' = timeOracle + 1
                                                  /\ pc' = [pc EXCEPT !["head"] = "dirtyWrite_h"]
                                                  /\ UNCHANGED objLogs
                                             ELSE /\ objLogs' = [objLogs EXCEPT ![head][req_h'.op.obj] = CommitDirtyVersion(@, req_h'.op)]
                                                  /\ pc' = [pc EXCEPT !["head"] = "respToClient"]
                                                  /\ UNCHANGED << timeOracle, 
                                                                  now_h >>
                 /\ UNCHANGED << objTotalOrders, allSubmittedOps, 
                                 terminatedYet, initClient, nonInitClients, 
                                 start, uninitializedObjs, initObj, objs_init, 
                                 obj_init, actions_init, action_init, 
                                 gateway_cinit, i_init, msg_cinit, 
                                 uniqueId_cinit, objs, obj, actions, action, 
                                 gateway_c, i, msg_c, uniqueId, sender_h, 
                                 pendingInvos_h, req_t, sender_t, 
                                 pendingInvos_t, now_t, req, sender, now, 
                                 pendingInvos >>

apportionQ_h == /\ pc["head"] = "apportionQ_h"
                /\ msgQs' = [msgQs EXCEPT ![<<head, tail>>] = Append(@, req_h)]
                /\ pendingInvos_h' = (pendingInvos_h \cup {<<(req_h.uniqueId), sender_h>>})
                /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
                /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                                terminatedYet, initClient, nonInitClients, 
                                start, timeOracle, uninitializedObjs, initObj, 
                                objs_init, obj_init, actions_init, action_init, 
                                gateway_cinit, i_init, msg_cinit, 
                                uniqueId_cinit, objs, obj, actions, action, 
                                gateway_c, i, msg_c, uniqueId, req_h, sender_h, 
                                now_h, req_t, sender_t, pendingInvos_t, now_t, 
                                req, sender, now, pendingInvos >>

addReadTO_h == /\ pc["head"] = "addReadTO_h"
               /\ req_h' = [ callType |-> READ_RESP,
                             uniqueId |-> req_h.uniqueId,
                             startTs |-> timeOracle,
                             commitTs |-> timeOracle,
                             op |-> Read(head, req_h.op.obj)]
               /\ objTotalOrders' = [objTotalOrders EXCEPT ![req_h'.op.obj] = Cons(req_h', @)]
               /\ pc' = [pc EXCEPT !["head"] = "respFromHead"]
               /\ UNCHANGED << msgQs, objLogs, allSubmittedOps, terminatedYet, 
                               initClient, nonInitClients, start, timeOracle, 
                               uninitializedObjs, initObj, objs_init, obj_init, 
                               actions_init, action_init, gateway_cinit, 
                               i_init, msg_cinit, uniqueId_cinit, objs, obj, 
                               actions, action, gateway_c, i, msg_c, uniqueId, 
                               sender_h, pendingInvos_h, now_h, req_t, 
                               sender_t, pendingInvos_t, now_t, req, sender, 
                               now, pendingInvos >>

respFromHead == /\ pc["head"] = "respFromHead"
                /\ msgQs' = [msgQs EXCEPT ![<<head, sender_h>>] = Append(@, req_h)]
                /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
                /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                                terminatedYet, initClient, nonInitClients, 
                                start, timeOracle, uninitializedObjs, initObj, 
                                objs_init, obj_init, actions_init, action_init, 
                                gateway_cinit, i_init, msg_cinit, 
                                uniqueId_cinit, objs, obj, actions, action, 
                                gateway_c, i, msg_c, uniqueId, req_h, sender_h, 
                                pendingInvos_h, now_h, req_t, sender_t, 
                                pendingInvos_t, now_t, req, sender, now, 
                                pendingInvos >>

readResp_h == /\ pc["head"] = "readResp_h"
              /\ msgQs' = [msgQs EXCEPT ![<<head, (Find(pendingInvos_h, req_h.uniqueId))>>] = Append(@, req_h)]
              /\ pendingInvos_h' = pendingInvos_h \ {FindPair(pendingInvos_h, (req_h.uniqueId))}
              /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
              /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                              terminatedYet, initClient, nonInitClients, start, 
                              timeOracle, uninitializedObjs, initObj, 
                              objs_init, obj_init, actions_init, action_init, 
                              gateway_cinit, i_init, msg_cinit, uniqueId_cinit, 
                              objs, obj, actions, action, gateway_c, i, msg_c, 
                              uniqueId, req_h, sender_h, now_h, req_t, 
                              sender_t, pendingInvos_t, now_t, req, sender, 
                              now, pendingInvos >>

dirtyWrite_h == /\ pc["head"] = "dirtyWrite_h"
                /\ req_h' = [req_h EXCEPT    !.startTs = now_h,
                                             !.op.writeStartTs = now_h,
                                             !.op.commitStatus = DIRTY]
                /\ objLogs' = [objLogs EXCEPT ![head][(req_h'.op).obj] = Cons((req_h'.op), @)]
                /\ pc' = [pc EXCEPT !["head"] = "propagate_h"]
                /\ UNCHANGED << msgQs, objTotalOrders, allSubmittedOps, 
                                terminatedYet, initClient, nonInitClients, 
                                start, timeOracle, uninitializedObjs, initObj, 
                                objs_init, obj_init, actions_init, action_init, 
                                gateway_cinit, i_init, msg_cinit, 
                                uniqueId_cinit, objs, obj, actions, action, 
                                gateway_c, i, msg_c, uniqueId, sender_h, 
                                pendingInvos_h, now_h, req_t, sender_t, 
                                pendingInvos_t, now_t, req, sender, now, 
                                pendingInvos >>

propagate_h == /\ pc["head"] = "propagate_h"
               /\ msgQs' = [msgQs EXCEPT ![<<head, (Successors[head])>>] = Append(@, req_h)]
               /\ pendingInvos_h' = (pendingInvos_h \cup {<<(req_h.uniqueId), sender_h>>})
               /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
               /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                               terminatedYet, initClient, nonInitClients, 
                               start, timeOracle, uninitializedObjs, initObj, 
                               objs_init, obj_init, actions_init, action_init, 
                               gateway_cinit, i_init, msg_cinit, 
                               uniqueId_cinit, objs, obj, actions, action, 
                               gateway_c, i, msg_c, uniqueId, req_h, sender_h, 
                               now_h, req_t, sender_t, pendingInvos_t, now_t, 
                               req, sender, now, pendingInvos >>

respToClient == /\ pc["head"] = "respToClient"
                /\ msgQs' = [msgQs EXCEPT ![<<head, (Find(pendingInvos_h, req_h.uniqueId))>>] = Append(@, req_h)]
                /\ pendingInvos_h' = pendingInvos_h \ {FindPair(pendingInvos_h, (req_h.uniqueId))}
                /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
                /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                                terminatedYet, initClient, nonInitClients, 
                                start, timeOracle, uninitializedObjs, initObj, 
                                objs_init, obj_init, actions_init, action_init, 
                                gateway_cinit, i_init, msg_cinit, 
                                uniqueId_cinit, objs, obj, actions, action, 
                                gateway_c, i, msg_c, uniqueId, req_h, sender_h, 
                                now_h, req_t, sender_t, pendingInvos_t, now_t, 
                                req, sender, now, pendingInvos >>

he == listen_h \/ incomingMsg_h \/ apportionQ_h \/ addReadTO_h
         \/ respFromHead \/ readResp_h \/ dirtyWrite_h \/ propagate_h
         \/ respToClient

listen_t == /\ pc["tail"] = "listen_t"
            /\ \E temp \in {s \in SendersTo(tail) : msgQs[<<s, tail>>] /= << >>}:
                 sender_t' = temp
            /\ pc' = [pc EXCEPT !["tail"] = "incomingMsg_t"]
            /\ UNCHANGED << msgQs, objLogs, objTotalOrders, allSubmittedOps, 
                            terminatedYet, initClient, nonInitClients, start, 
                            timeOracle, uninitializedObjs, initObj, objs_init, 
                            obj_init, actions_init, action_init, gateway_cinit, 
                            i_init, msg_cinit, uniqueId_cinit, objs, obj, 
                            actions, action, gateway_c, i, msg_c, uniqueId, 
                            req_h, sender_h, pendingInvos_h, now_h, req_t, 
                            pendingInvos_t, now_t, req, sender, now, 
                            pendingInvos >>

incomingMsg_t == /\ pc["tail"] = "incomingMsg_t"
                 /\ req_t' = Head(msgQs[<<sender_t, tail>>])
                 /\ msgQs' = [msgQs EXCEPT ![<<sender_t, tail>>] = Tail(@)]
                 /\ IF req_t'.callType = READ_INV
                       THEN /\ now_t' = timeOracle
                            /\ timeOracle' = timeOracle + 1
                            /\ pc' = [pc EXCEPT !["tail"] = "addReadTO_t"]
                            /\ UNCHANGED objLogs
                       ELSE /\ now_t' = timeOracle
                            /\ timeOracle' = timeOracle + 1
                            /\ objLogs' = [objLogs EXCEPT ![tail][([req_t'.op EXCEPT  !.writeCommitTs = now_t',
                                                                                      !.commitStatus = CLEAN]).obj] = Cons(([req_t'.op EXCEPT  !.writeCommitTs = now_t',
                                                                                                                                               !.commitStatus = CLEAN]), @)]
                            /\ pc' = [pc EXCEPT !["tail"] = "addWriteTO_t"]
                 /\ UNCHANGED << objTotalOrders, allSubmittedOps, 
                                 terminatedYet, initClient, nonInitClients, 
                                 start, uninitializedObjs, initObj, objs_init, 
                                 obj_init, actions_init, action_init, 
                                 gateway_cinit, i_init, msg_cinit, 
                                 uniqueId_cinit, objs, obj, actions, action, 
                                 gateway_c, i, msg_c, uniqueId, req_h, 
                                 sender_h, pendingInvos_h, now_h, sender_t, 
                                 pendingInvos_t, req, sender, now, 
                                 pendingInvos >>

addReadTO_t == /\ pc["tail"] = "addReadTO_t"
               /\ req_t' = [ callType |-> READ_RESP,
                             uniqueId |-> req_t.uniqueId,
                             startTs |-> now_t,
                             commitTs |-> now_t,
                             op |-> Read(tail, req_t.op.obj)]
               /\ objTotalOrders' = [objTotalOrders EXCEPT ![req_t'.op.obj] = Cons(req_t', @)]
               /\ pc' = [pc EXCEPT !["tail"] = "respFromSelf_t"]
               /\ UNCHANGED << msgQs, objLogs, allSubmittedOps, terminatedYet, 
                               initClient, nonInitClients, start, timeOracle, 
                               uninitializedObjs, initObj, objs_init, obj_init, 
                               actions_init, action_init, gateway_cinit, 
                               i_init, msg_cinit, uniqueId_cinit, objs, obj, 
                               actions, action, gateway_c, i, msg_c, uniqueId, 
                               req_h, sender_h, pendingInvos_h, now_h, 
                               sender_t, pendingInvos_t, now_t, req, sender, 
                               now, pendingInvos >>

respFromSelf_t == /\ pc["tail"] = "respFromSelf_t"
                  /\ msgQs' = [msgQs EXCEPT ![<<tail, sender_t>>] = Append(@, req_t)]
                  /\ pc' = [pc EXCEPT !["tail"] = "listen_t"]
                  /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                                  terminatedYet, initClient, nonInitClients, 
                                  start, timeOracle, uninitializedObjs, 
                                  initObj, objs_init, obj_init, actions_init, 
                                  action_init, gateway_cinit, i_init, 
                                  msg_cinit, uniqueId_cinit, objs, obj, 
                                  actions, action, gateway_c, i, msg_c, 
                                  uniqueId, req_h, sender_h, pendingInvos_h, 
                                  now_h, req_t, sender_t, pendingInvos_t, 
                                  now_t, req, sender, now, pendingInvos >>

addWriteTO_t == /\ pc["tail"] = "addWriteTO_t"
                /\ req_t' = [    callType |-> WRITE_RESP,
                                 uniqueId |-> req_t.uniqueId,
                                 startTs |-> req_t.startTs,
                                 commitTs |-> Read(tail, req_t.op.obj).writeCommitTs,
                                 op |-> Read(tail, req_t.op.obj)]
                /\ objTotalOrders' = [objTotalOrders EXCEPT ![req_t'.op.obj] = Cons(req_t', @)]
                /\ pc' = [pc EXCEPT !["tail"] = "tailAck"]
                /\ UNCHANGED << msgQs, objLogs, allSubmittedOps, terminatedYet, 
                                initClient, nonInitClients, start, timeOracle, 
                                uninitializedObjs, initObj, objs_init, 
                                obj_init, actions_init, action_init, 
                                gateway_cinit, i_init, msg_cinit, 
                                uniqueId_cinit, objs, obj, actions, action, 
                                gateway_c, i, msg_c, uniqueId, req_h, sender_h, 
                                pendingInvos_h, now_h, sender_t, 
                                pendingInvos_t, now_t, req, sender, now, 
                                pendingInvos >>

tailAck == /\ pc["tail"] = "tailAck"
           /\ msgQs' = [msgQs EXCEPT ![<<tail, (Predecessors[tail])>>] = Append(@, req_t)]
           /\ pc' = [pc EXCEPT !["tail"] = "listen_t"]
           /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                           terminatedYet, initClient, nonInitClients, start, 
                           timeOracle, uninitializedObjs, initObj, objs_init, 
                           obj_init, actions_init, action_init, gateway_cinit, 
                           i_init, msg_cinit, uniqueId_cinit, objs, obj, 
                           actions, action, gateway_c, i, msg_c, uniqueId, 
                           req_h, sender_h, pendingInvos_h, now_h, req_t, 
                           sender_t, pendingInvos_t, now_t, req, sender, now, 
                           pendingInvos >>

ta == listen_t \/ incomingMsg_t \/ addReadTO_t \/ respFromSelf_t
         \/ addWriteTO_t \/ tailAck

listen(self) == /\ pc[self] = "listen"
                /\ \E temp \in {s \in SendersTo(self) : msgQs[<<s, self>>] /= << >>}:
                     sender' = [sender EXCEPT ![self] = temp]
                /\ pc' = [pc EXCEPT ![self] = "incomingMsg"]
                /\ UNCHANGED << msgQs, objLogs, objTotalOrders, 
                                allSubmittedOps, terminatedYet, initClient, 
                                nonInitClients, start, timeOracle, 
                                uninitializedObjs, initObj, objs_init, 
                                obj_init, actions_init, action_init, 
                                gateway_cinit, i_init, msg_cinit, 
                                uniqueId_cinit, objs, obj, actions, action, 
                                gateway_c, i, msg_c, uniqueId, req_h, sender_h, 
                                pendingInvos_h, now_h, req_t, sender_t, 
                                pendingInvos_t, now_t, req, now, pendingInvos >>

incomingMsg(self) == /\ pc[self] = "incomingMsg"
                     /\ req' = [req EXCEPT ![self] = Head(msgQs[<<sender[self], self>>])]
                     /\ msgQs' = [msgQs EXCEPT ![<<sender[self], self>>] = Tail(@)]
                     /\ IF req'[self].callType = READ_INV
                           THEN /\ IF IsDirty(self, req'[self].op.obj)
                                      THEN /\ pc' = [pc EXCEPT ![self] = "apportionQ"]
                                           /\ UNCHANGED << timeOracle, now >>
                                      ELSE /\ now' = [now EXCEPT ![self] = timeOracle]
                                           /\ timeOracle' = timeOracle + 1
                                           /\ pc' = [pc EXCEPT ![self] = "addReadTO"]
                                /\ UNCHANGED objLogs
                           ELSE /\ IF req'[self].callType = READ_RESP
                                      THEN /\ pc' = [pc EXCEPT ![self] = "fwdFromTail"]
                                           /\ UNCHANGED objLogs
                                      ELSE /\ IF req'[self].callType = WRITE_INV
                                                 THEN /\ objLogs' = [objLogs EXCEPT ![self][(req'[self].op).obj] = Cons((req'[self].op), @)]
                                                      /\ pc' = [pc EXCEPT ![self] = "propagate"]
                                                 ELSE /\ objLogs' = [objLogs EXCEPT ![self][req'[self].op.obj] = CommitDirtyVersion(@, req'[self].op)]
                                                      /\ pc' = [pc EXCEPT ![self] = "backProp"]
                                /\ UNCHANGED << timeOracle, now >>
                     /\ UNCHANGED << objTotalOrders, allSubmittedOps, 
                                     terminatedYet, initClient, nonInitClients, 
                                     start, uninitializedObjs, initObj, 
                                     objs_init, obj_init, actions_init, 
                                     action_init, gateway_cinit, i_init, 
                                     msg_cinit, uniqueId_cinit, objs, obj, 
                                     actions, action, gateway_c, i, msg_c, 
                                     uniqueId, req_h, sender_h, pendingInvos_h, 
                                     now_h, req_t, sender_t, pendingInvos_t, 
                                     now_t, sender, pendingInvos >>

apportionQ(self) == /\ pc[self] = "apportionQ"
                    /\ msgQs' = [msgQs EXCEPT ![<<self, tail>>] = Append(@, req[self])]
                    /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \cup {<<(req[self].uniqueId), sender[self]>>}]
                    /\ pc' = [pc EXCEPT ![self] = "listen"]
                    /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                                    terminatedYet, initClient, nonInitClients, 
                                    start, timeOracle, uninitializedObjs, 
                                    initObj, objs_init, obj_init, actions_init, 
                                    action_init, gateway_cinit, i_init, 
                                    msg_cinit, uniqueId_cinit, objs, obj, 
                                    actions, action, gateway_c, i, msg_c, 
                                    uniqueId, req_h, sender_h, pendingInvos_h, 
                                    now_h, req_t, sender_t, pendingInvos_t, 
                                    now_t, req, sender, now >>

addReadTO(self) == /\ pc[self] = "addReadTO"
                   /\ req' = [req EXCEPT ![self] = [callType |-> READ_RESP,
                                                    uniqueId |-> req[self].uniqueId,
                                                    startTs |-> now[self],
                                                    commitTs |-> now[self],
                                                    op |-> Read(self, req[self].op.obj)]]
                   /\ objTotalOrders' = [objTotalOrders EXCEPT ![req'[self].op.obj] = Cons(req'[self], @)]
                   /\ pc' = [pc EXCEPT ![self] = "respFromSelf"]
                   /\ UNCHANGED << msgQs, objLogs, allSubmittedOps, 
                                   terminatedYet, initClient, nonInitClients, 
                                   start, timeOracle, uninitializedObjs, 
                                   initObj, objs_init, obj_init, actions_init, 
                                   action_init, gateway_cinit, i_init, 
                                   msg_cinit, uniqueId_cinit, objs, obj, 
                                   actions, action, gateway_c, i, msg_c, 
                                   uniqueId, req_h, sender_h, pendingInvos_h, 
                                   now_h, req_t, sender_t, pendingInvos_t, 
                                   now_t, sender, now, pendingInvos >>

respFromSelf(self) == /\ pc[self] = "respFromSelf"
                      /\ msgQs' = [msgQs EXCEPT ![<<self, sender[self]>>] = Append(@, req[self])]
                      /\ pc' = [pc EXCEPT ![self] = "listen"]
                      /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                                      terminatedYet, initClient, 
                                      nonInitClients, start, timeOracle, 
                                      uninitializedObjs, initObj, objs_init, 
                                      obj_init, actions_init, action_init, 
                                      gateway_cinit, i_init, msg_cinit, 
                                      uniqueId_cinit, objs, obj, actions, 
                                      action, gateway_c, i, msg_c, uniqueId, 
                                      req_h, sender_h, pendingInvos_h, now_h, 
                                      req_t, sender_t, pendingInvos_t, now_t, 
                                      req, sender, now, pendingInvos >>

fwdFromTail(self) == /\ pc[self] = "fwdFromTail"
                     /\ msgQs' = [msgQs EXCEPT ![<<self, (Find(pendingInvos[self], req[self].uniqueId))>>] = Append(@, req[self])]
                     /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \ {FindPair(pendingInvos[self], (req[self].uniqueId))}]
                     /\ pc' = [pc EXCEPT ![self] = "listen"]
                     /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                                     terminatedYet, initClient, nonInitClients, 
                                     start, timeOracle, uninitializedObjs, 
                                     initObj, objs_init, obj_init, 
                                     actions_init, action_init, gateway_cinit, 
                                     i_init, msg_cinit, uniqueId_cinit, objs, 
                                     obj, actions, action, gateway_c, i, msg_c, 
                                     uniqueId, req_h, sender_h, pendingInvos_h, 
                                     now_h, req_t, sender_t, pendingInvos_t, 
                                     now_t, req, sender, now >>

propagate(self) == /\ pc[self] = "propagate"
                   /\ msgQs' = [msgQs EXCEPT ![<<self, (Successors[self])>>] = Append(@, req[self])]
                   /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \cup {<<(req[self].uniqueId), sender[self]>>}]
                   /\ pc' = [pc EXCEPT ![self] = "listen"]
                   /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                                   terminatedYet, initClient, nonInitClients, 
                                   start, timeOracle, uninitializedObjs, 
                                   initObj, objs_init, obj_init, actions_init, 
                                   action_init, gateway_cinit, i_init, 
                                   msg_cinit, uniqueId_cinit, objs, obj, 
                                   actions, action, gateway_c, i, msg_c, 
                                   uniqueId, req_h, sender_h, pendingInvos_h, 
                                   now_h, req_t, sender_t, pendingInvos_t, 
                                   now_t, req, sender, now >>

backProp(self) == /\ pc[self] = "backProp"
                  /\ msgQs' = [msgQs EXCEPT ![<<self, (Find(pendingInvos[self], req[self].uniqueId))>>] = Append(@, req[self])]
                  /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \ {FindPair(pendingInvos[self], (req[self].uniqueId))}]
                  /\ pc' = [pc EXCEPT ![self] = "listen"]
                  /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                                  terminatedYet, initClient, nonInitClients, 
                                  start, timeOracle, uninitializedObjs, 
                                  initObj, objs_init, obj_init, actions_init, 
                                  action_init, gateway_cinit, i_init, 
                                  msg_cinit, uniqueId_cinit, objs, obj, 
                                  actions, action, gateway_c, i, msg_c, 
                                  uniqueId, req_h, sender_h, pendingInvos_h, 
                                  now_h, req_t, sender_t, pendingInvos_t, 
                                  now_t, req, sender, now >>

n(self) == listen(self) \/ incomingMsg(self) \/ apportionQ(self)
              \/ addReadTO(self) \/ respFromSelf(self) \/ fwdFromTail(self)
              \/ propagate(self) \/ backProp(self)

Next == iclient \/ he \/ ta
           \/ (\E self \in nonInitClients: c(self))
           \/ (\E self \in Nodes \ {head, tail}: n(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ WF_vars(iclient)
        /\ \A self \in nonInitClients : WF_vars(c(self))
        /\ WF_vars(he)
        /\ WF_vars(ta)
        /\ \A self \in Nodes \ {head, tail} : WF_vars(n(self))

\* END TRANSLATION 



GlobalTypeInvariant ==  /\ msgQs \in [Network -> {<< >>} \cup Seq(RequestType)]
                        /\ objLogs \in [Nodes -> [Objects -> {<< >>} \cup Seq(ObjectVersionType)]]
                        /\ objTotalOrders \in [Objects -> Seq(RequestType)]
\*                        /\ allSubmittedOps \in [Objects -> {RequestType}]
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
                            /\ i_init \in Nat
                            /\ msg_cinit \in RequestType \cup {NullReq}
                            /\ uniqueId_cinit \in UniqueIdType \cup {NullUniqueId}
                            
ClientTypeInvariant ==  \*/\ \A objInited \in objs: objInited \in [Clients -> Objects]
                        /\ obj \in [Clients \ {initClient} -> Objects]
\*                        /\ actions \in [Clients \ {initClient} -> Seq({WRITE_INV, READ_INV})]
                        /\ action \in [Clients \ {initClient} -> {WRITE_INV, READ_INV}]
                        /\ gateway_c \in [Clients \ {initClient} -> Nodes \cup {NullNode}]
                        /\ i \in [Clients \ {initClient} -> Nat]
                        /\ msg_c \in [Clients \ {initClient} -> RequestType \cup {NullReq}]
                        /\ uniqueId \in [Clients \ {initClient} -> UniqueIdType]

\*ClientTypeInvariant ==  /\ uniqueId \in [Clients -> UniqueIdType]
\*                        /\ msg \in [Clients -> RequestType \cup {NullReq}]
\*                        /\ gateway \in [Clients -> Nodes \cup {NullNode}]

                        
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

RECURSIVE MostRecentWrite(_)
MostRecentWrite(totalOrder) == IF totalOrder = << >> THEN NullReq
                                ELSE    CASE Head(totalOrder).callType = WRITE_RESP -> Head(totalOrder)
                                        [] Head(totalOrder).callType = READ_RESP -> MostRecentWrite(Tail(totalOrder))

RECURSIVE ReadPrecededByWrite(_)                                
ReadPrecededByWrite(totalOrder) == IF totalOrder = << >> THEN TRUE
                                    ELSE LET reqOp == Head(totalOrder)
                                             remainder == Tail(totalOrder) IN
                                                CASE reqOp.callType = WRITE_RESP -> ReadPrecededByWrite(remainder)
                                                [] reqOp.callType = READ_RESP -> LET pastWrite == MostRecentWrite(remainder) IN
                                                                                    CASE pastWrite = NullReq -> FALSE
                                                                                    [] reqOp.op.uniqueId = pastWrite.op.uniqueId -> 
                                                                                        ReadPrecededByWrite(remainder)
                                                                                    [] OTHER -> FALSE
                                                                    
\*RealtimeDependency(successor, predecessor) == predecessor.commitTs < successor.startTs
\*IsConcurrent(reqOp1, reqOp2) == ~(  \/ RealtimeDependency(reqOp1, reqOp2)
\*                                    \/ RealtimeDependency(reqOp1, reqOp2))
\*                                                                    
\*RECURSIVE IsConcurrentUntilLessThan(_, _)
\*IsConcurrentUntilLessThan(op, remainder) == IF remainder = << >> THEN TRUE ELSE
\*                                                    LET nextOp == Head(remainder) IN
\*                                                    CASE RealtimeDependency(op, nextOp) -> TRUE
\*                                                    [] IsConcurrent(op, nextOp) -> 
\*                                                        IsConcurrentUntilLessThan(op, Tail(remainder))
\*                                                    [] OTHER -> FALSE
\*                                                 
\*RECURSIVE RespectsRealtime(_)
\*RespectsRealtime(totalOrder) == IF totalOrder = << >> 
\*                                THEN TRUE
\*                                ELSE IF IsConcurrentUntilLessThan(Head(totalOrder), Tail(totalOrder)) 
\*                                        THEN RespectsRealtime(Tail(totalOrder))
\*                                        ELSE FALSE


IsLegal(totalOrder) ==  /\ ReadPrecededByWrite(totalOrder)
\*                        /\ RespectsRealtime(totalOrder)

LegalOrderInvariant == \A o \in Objects: IsLegal(objTotalOrders[o])


RECURSIVE ContainsAllOps(_, _)                        
ContainsAllOps(totalOrder, setOfOps) == CASE setOfOps = {} -> TRUE
                                        [] totalOrder = << >> /\ setOfOps /= {} -> FALSE
                                        [] \E reqOp \in setOfOps : reqOp = Head(totalOrder) -> 
                                            ContainsAllOps(Tail(totalOrder), setOfOps \ {Head(totalOrder)})
                                        [] OTHER -> ContainsAllOps(Tail(totalOrder), setOfOps)  \* newly committed op,
                                                                                                \* not yet in total order
                                            
TotalOrderInvariant == \A o \in Objects: ContainsAllOps(objTotalOrders[o], allSubmittedOps[o])
                                            
IsTotal(totalOrder, setOfOps) ==    /\ ContainsAllOps(totalOrder, setOfOps)
                                    /\ Len(totalOrder) = Cardinality(setOfOps) 
                                    

IsObjLinearizable(totalOrder, setOfOps) ==  /\ IsLegal(totalOrder)
                                            /\ IsTotal(totalOrder, setOfOps) 
                                
Linearizability == \A o \in Objects: IsObjLinearizable(objTotalOrders[o], allSubmittedOps[o])

Terminated == \A client \in Clients: terminatedYet[client] = TRUE

=============================================================================
\* Modification History
\* Last modified Sat Jun 17 03:26:39 EDT 2023 by 72jen
\* Last modified Thu Jun 15 15:19:09 EDT 2023 by jenniferlam
\* Created Tue Jun 13 12:56:59 EDT 2023 by jenniferlam
