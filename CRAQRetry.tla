----------------------------- MODULE CRAQRetry -----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Clients, Nodes, head, tail, NumWrites, NumReads, Objects, MaxTimestamp, initClient

NumMsgs == 10

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
\*        /\ Cardinality(UniqueIdType) = Cardinality(Clients) * (NumMsgs + 1)
        
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
\*NullObj == CHOOSE o : o \notin Objects
\*NullClient == CHOOSE c : c \notin Clients
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
            };

        };
        
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
            };
            actions := {WRITE_INV, READ_INV}; 
            
        };
        
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
        
        terminate: terminatedYet[self] := TRUE;
    }
   
    
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
            
\*            incomingMsg_h:
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
            
\*            incomingMsg_t:
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
            } else { \* WRITE_INV
                now_t := timeOracle;
                timeOracle := timeOracle + 1;
                write(tail, [req_t.op EXCEPT  !.writeCommitTs = now_t, 
                                              !.commitStatus = CLEAN]);
                tailAck: req_t := [    callType |-> WRITE_RESP,
                                            uniqueId |-> req_t.uniqueId,
                                            startTs |-> req_t.startTs,
                                            commitTs |-> Read(tail, req_t.op.obj).writeCommitTs,
                                            op |-> Read(tail, req_t.op.obj)];
                send(tail, Predecessors[tail], req_t);   
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
            
\*            incomingMsg:
            when msgQs[<<sender, self>>] /= << >>;  
            recv(sender, self, req); 
            
            if (req.callType = READ_INV) {
                if (IsDirty(self, req.op.obj)) {                 
                    apportionQ: send(self, tail, req);
                    add(pendingInvos, req.uniqueId, sender);
                } else {
                    now := timeOracle;
                    timeOracle := timeOracle + 1;
                    respFromSelf: req :=  [callType |-> READ_RESP,
                                        uniqueId |-> req.uniqueId,
                                        startTs |-> now,
                                        commitTs |-> now,
                                        op |-> Read(self, req.op.obj)];
                    send(self, sender, req);
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
\* BEGIN TRANSLATION (chksum(pcal) = "36c979e5" /\ chksum(tla) = "362f3a2")
VARIABLES msgQs, objLogs, allSubmittedWriteOps, allSubmittedReadOps, 
          terminatedYet, nonInitClients, start, timeOracle, pc

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
          action_init, gateway_cinit, msg_cinit, uniqueId_cinit, sentOps_init, 
          recvdOps_init, objs, obj, actions, action, gateway_c, msg_c, 
          uniqueId, sentOps, recvdOps, req_h, sender_h, pendingInvos_h, now_h, 
          req_t, sender_t, pendingInvos_t, now_t, req, sender, now, 
          pendingInvos

vars == << msgQs, objLogs, allSubmittedWriteOps, allSubmittedReadOps, 
           terminatedYet, nonInitClients, start, timeOracle, pc, 
           uninitializedObjs, initObj, objs_init, obj_init, actions_init, 
           action_init, gateway_cinit, msg_cinit, uniqueId_cinit, 
           sentOps_init, recvdOps_init, objs, obj, actions, action, gateway_c, 
           msg_c, uniqueId, sentOps, recvdOps, req_h, sender_h, 
           pendingInvos_h, now_h, req_t, sender_t, pendingInvos_t, now_t, req, 
           sender, now, pendingInvos >>

ProcSet == {"initClient"} \cup (nonInitClients) \cup {"head"} \cup {"tail"} \cup (Nodes \ {head, tail})

Init == (* Global variables *)
        /\ msgQs = [edge \in Network |-> << >>]
        /\ objLogs = [n \in Nodes |-> [o \in Objects |-> << >>]]
        /\ allSubmittedWriteOps = [o \in Objects |-> {}]
        /\ allSubmittedReadOps = [ o \in Objects |-> {}]
        /\ terminatedYet = [c \in Clients |-> FALSE]
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
                            /\ pc' = [pc EXCEPT !["initClient"] = "waitFor_init"]
                            /\ start' = start
                       ELSE /\ start' = TRUE
                            /\ pc' = [pc EXCEPT !["initClient"] = "concurrentOps_init"]
                            /\ UNCHANGED << msgQs, uninitializedObjs, initObj, 
                                            uniqueId_cinit >>
                 /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                                 allSubmittedReadOps, terminatedYet, 
                                 nonInitClients, timeOracle, objs_init, 
                                 obj_init, actions_init, action_init, 
                                 gateway_cinit, msg_cinit, sentOps_init, 
                                 recvdOps_init, objs, obj, actions, action, 
                                 gateway_c, msg_c, uniqueId, sentOps, recvdOps, 
                                 req_h, sender_h, pendingInvos_h, now_h, req_t, 
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
                                timeOracle, uninitializedObjs, initObj, 
                                objs_init, obj_init, actions_init, action_init, 
                                gateway_cinit, uniqueId_cinit, sentOps_init, 
                                recvdOps_init, objs, obj, actions, action, 
                                gateway_c, msg_c, uniqueId, sentOps, recvdOps, 
                                req_h, sender_h, pendingInvos_h, now_h, req_t, 
                                sender_t, pendingInvos_t, now_t, req, sender, 
                                now, pendingInvos >>

concurrentOps_init == /\ pc["initClient"] = "concurrentOps_init"
                      /\ IF objs_init /= {}
                            THEN /\ obj_init' = (CHOOSE o \in objs_init: TRUE)
                                 /\ objs_init' = objs_init \ {obj_init'}
                                 /\ actions_init' = {WRITE_INV, READ_INV}
                                 /\ pc' = [pc EXCEPT !["initClient"] = "readOrWrite_init"]
                            ELSE /\ pc' = [pc EXCEPT !["initClient"] = "waitForOps_init"]
                                 /\ UNCHANGED << objs_init, obj_init, 
                                                 actions_init >>
                      /\ UNCHANGED << msgQs, objLogs, allSubmittedWriteOps, 
                                      allSubmittedReadOps, terminatedYet, 
                                      nonInitClients, start, timeOracle, 
                                      uninitializedObjs, initObj, action_init, 
                                      gateway_cinit, msg_cinit, uniqueId_cinit, 
                                      sentOps_init, recvdOps_init, objs, obj, 
                                      actions, action, gateway_c, msg_c, 
                                      uniqueId, sentOps, recvdOps, req_h, 
                                      sender_h, pendingInvos_h, now_h, req_t, 
                                      sender_t, pendingInvos_t, now_t, req, 
                                      sender, now, pendingInvos >>

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
                               /\ pc' = [pc EXCEPT !["initClient"] = "readOrWrite_init"]
                          ELSE /\ pc' = [pc EXCEPT !["initClient"] = "concurrentOps_init"]
                               /\ UNCHANGED << msgQs, actions_init, 
                                               action_init, uniqueId_cinit, 
                                               sentOps_init >>
                    /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                                    allSubmittedReadOps, terminatedYet, 
                                    nonInitClients, start, timeOracle, 
                                    uninitializedObjs, initObj, objs_init, 
                                    obj_init, gateway_cinit, msg_cinit, 
                                    recvdOps_init, objs, obj, actions, action, 
                                    gateway_c, msg_c, uniqueId, sentOps, 
                                    recvdOps, req_h, sender_h, pendingInvos_h, 
                                    now_h, req_t, sender_t, pendingInvos_t, 
                                    now_t, req, sender, now, pendingInvos >>

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
                         ELSE /\ pc' = [pc EXCEPT !["initClient"] = "terminate_init"]
                              /\ UNCHANGED << msgQs, allSubmittedWriteOps, 
                                              allSubmittedReadOps, 
                                              gateway_cinit, msg_cinit, 
                                              recvdOps_init >>
                   /\ UNCHANGED << objLogs, terminatedYet, nonInitClients, 
                                   start, timeOracle, uninitializedObjs, 
                                   initObj, objs_init, obj_init, actions_init, 
                                   action_init, uniqueId_cinit, sentOps_init, 
                                   objs, obj, actions, action, gateway_c, 
                                   msg_c, uniqueId, sentOps, recvdOps, req_h, 
                                   sender_h, pendingInvos_h, now_h, req_t, 
                                   sender_t, pendingInvos_t, now_t, req, 
                                   sender, now, pendingInvos >>

terminate_init == /\ pc["initClient"] = "terminate_init"
                  /\ terminatedYet' = [terminatedYet EXCEPT ![initClient] = TRUE]
                  /\ pc' = [pc EXCEPT !["initClient"] = "Done"]
                  /\ UNCHANGED << msgQs, objLogs, allSubmittedWriteOps, 
                                  allSubmittedReadOps, nonInitClients, start, 
                                  timeOracle, uninitializedObjs, initObj, 
                                  objs_init, obj_init, actions_init, 
                                  action_init, gateway_cinit, msg_cinit, 
                                  uniqueId_cinit, sentOps_init, recvdOps_init, 
                                  objs, obj, actions, action, gateway_c, msg_c, 
                                  uniqueId, sentOps, recvdOps, req_h, sender_h, 
                                  pendingInvos_h, now_h, req_t, sender_t, 
                                  pendingInvos_t, now_t, req, sender, now, 
                                  pendingInvos >>

iclient == initializeObj \/ waitFor_init \/ concurrentOps_init
              \/ readOrWrite_init \/ waitForOps_init \/ terminate_init

waitForInit(self) == /\ pc[self] = "waitForInit"
                     /\ start = TRUE
                     /\ pc' = [pc EXCEPT ![self] = "concurrentOps"]
                     /\ UNCHANGED << msgQs, objLogs, allSubmittedWriteOps, 
                                     allSubmittedReadOps, terminatedYet, 
                                     nonInitClients, start, timeOracle, 
                                     uninitializedObjs, initObj, objs_init, 
                                     obj_init, actions_init, action_init, 
                                     gateway_cinit, msg_cinit, uniqueId_cinit, 
                                     sentOps_init, recvdOps_init, objs, obj, 
                                     actions, action, gateway_c, msg_c, 
                                     uniqueId, sentOps, recvdOps, req_h, 
                                     sender_h, pendingInvos_h, now_h, req_t, 
                                     sender_t, pendingInvos_t, now_t, req, 
                                     sender, now, pendingInvos >>

concurrentOps(self) == /\ pc[self] = "concurrentOps"
                       /\ IF objs[self] /= {}
                             THEN /\ obj' = [obj EXCEPT ![self] = CHOOSE o \in objs[self]: TRUE]
                                  /\ objs' = [objs EXCEPT ![self] = objs[self] \ {obj'[self]}]
                                  /\ pc' = [pc EXCEPT ![self] = "readOrWrite"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "waitForOps"]
                                  /\ UNCHANGED << objs, obj >>
                       /\ UNCHANGED << msgQs, objLogs, allSubmittedWriteOps, 
                                       allSubmittedReadOps, terminatedYet, 
                                       nonInitClients, start, timeOracle, 
                                       uninitializedObjs, initObj, objs_init, 
                                       obj_init, actions_init, action_init, 
                                       gateway_cinit, msg_cinit, 
                                       uniqueId_cinit, sentOps_init, 
                                       recvdOps_init, actions, action, 
                                       gateway_c, msg_c, uniqueId, sentOps, 
                                       recvdOps, req_h, sender_h, 
                                       pendingInvos_h, now_h, req_t, sender_t, 
                                       pendingInvos_t, now_t, req, sender, now, 
                                       pendingInvos >>

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
                                /\ pc' = [pc EXCEPT ![self] = "readOrWrite"]
                           ELSE /\ actions' = [actions EXCEPT ![self] = {WRITE_INV, READ_INV}]
                                /\ pc' = [pc EXCEPT ![self] = "concurrentOps"]
                                /\ UNCHANGED << msgQs, action, uniqueId, 
                                                sentOps >>
                     /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                                     allSubmittedReadOps, terminatedYet, 
                                     nonInitClients, start, timeOracle, 
                                     uninitializedObjs, initObj, objs_init, 
                                     obj_init, actions_init, action_init, 
                                     gateway_cinit, msg_cinit, uniqueId_cinit, 
                                     sentOps_init, recvdOps_init, objs, obj, 
                                     gateway_c, msg_c, recvdOps, req_h, 
                                     sender_h, pendingInvos_h, now_h, req_t, 
                                     sender_t, pendingInvos_t, now_t, req, 
                                     sender, now, pendingInvos >>

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
                                         "Failure of assertion at line 284, column 13.")
                               /\ recvdOps' = [recvdOps EXCEPT ![self] = recvdOps[self] + 1]
                               /\ pc' = [pc EXCEPT ![self] = "waitForOps"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "terminate"]
                               /\ UNCHANGED << msgQs, allSubmittedWriteOps, 
                                               allSubmittedReadOps, gateway_c, 
                                               msg_c, recvdOps >>
                    /\ UNCHANGED << objLogs, terminatedYet, nonInitClients, 
                                    start, timeOracle, uninitializedObjs, 
                                    initObj, objs_init, obj_init, actions_init, 
                                    action_init, gateway_cinit, msg_cinit, 
                                    uniqueId_cinit, sentOps_init, 
                                    recvdOps_init, objs, obj, actions, action, 
                                    uniqueId, sentOps, req_h, sender_h, 
                                    pendingInvos_h, now_h, req_t, sender_t, 
                                    pendingInvos_t, now_t, req, sender, now, 
                                    pendingInvos >>

terminate(self) == /\ pc[self] = "terminate"
                   /\ terminatedYet' = [terminatedYet EXCEPT ![self] = TRUE]
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << msgQs, objLogs, allSubmittedWriteOps, 
                                   allSubmittedReadOps, nonInitClients, start, 
                                   timeOracle, uninitializedObjs, initObj, 
                                   objs_init, obj_init, actions_init, 
                                   action_init, gateway_cinit, msg_cinit, 
                                   uniqueId_cinit, sentOps_init, recvdOps_init, 
                                   objs, obj, actions, action, gateway_c, 
                                   msg_c, uniqueId, sentOps, recvdOps, req_h, 
                                   sender_h, pendingInvos_h, now_h, req_t, 
                                   sender_t, pendingInvos_t, now_t, req, 
                                   sender, now, pendingInvos >>

c(self) == waitForInit(self) \/ concurrentOps(self) \/ readOrWrite(self)
              \/ waitForOps(self) \/ terminate(self)

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
                       /\ UNCHANGED objLogs
                  ELSE /\ IF req_h'.callType = READ_RESP
                             THEN /\ pc' = [pc EXCEPT !["head"] = "readResp_h"]
                                  /\ UNCHANGED << objLogs, timeOracle, now_h >>
                             ELSE /\ IF req_h'.callType = WRITE_INV
                                        THEN /\ now_h' = timeOracle
                                             /\ timeOracle' = timeOracle + 1
                                             /\ pc' = [pc EXCEPT !["head"] = "dirtyWrite_h"]
                                             /\ UNCHANGED objLogs
                                        ELSE /\ objLogs' = [objLogs EXCEPT ![head][req_h'.op.obj] = CommitDirtyVersion(@, req_h'.op)]
                                             /\ pc' = [pc EXCEPT !["head"] = "respToClient"]
                                             /\ UNCHANGED << timeOracle, now_h >>
            /\ UNCHANGED << allSubmittedWriteOps, allSubmittedReadOps, 
                            terminatedYet, nonInitClients, start, 
                            uninitializedObjs, initObj, objs_init, obj_init, 
                            actions_init, action_init, gateway_cinit, 
                            msg_cinit, uniqueId_cinit, sentOps_init, 
                            recvdOps_init, objs, obj, actions, action, 
                            gateway_c, msg_c, uniqueId, sentOps, recvdOps, 
                            pendingInvos_h, req_t, sender_t, pendingInvos_t, 
                            now_t, req, sender, now, pendingInvos >>

apportionQ_h == /\ pc["head"] = "apportionQ_h"
                /\ msgQs' = [msgQs EXCEPT ![<<head, tail>>] = Append(@, req_h)]
                /\ pendingInvos_h' = (pendingInvos_h \cup {<<(req_h.uniqueId), sender_h>>})
                /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
                /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                                allSubmittedReadOps, terminatedYet, 
                                nonInitClients, start, timeOracle, 
                                uninitializedObjs, initObj, objs_init, 
                                obj_init, actions_init, action_init, 
                                gateway_cinit, msg_cinit, uniqueId_cinit, 
                                sentOps_init, recvdOps_init, objs, obj, 
                                actions, action, gateway_c, msg_c, uniqueId, 
                                sentOps, recvdOps, req_h, sender_h, now_h, 
                                req_t, sender_t, pendingInvos_t, now_t, req, 
                                sender, now, pendingInvos >>

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
                                nonInitClients, start, timeOracle, 
                                uninitializedObjs, initObj, objs_init, 
                                obj_init, actions_init, action_init, 
                                gateway_cinit, msg_cinit, uniqueId_cinit, 
                                sentOps_init, recvdOps_init, objs, obj, 
                                actions, action, gateway_c, msg_c, uniqueId, 
                                sentOps, recvdOps, sender_h, pendingInvos_h, 
                                now_h, req_t, sender_t, pendingInvos_t, now_t, 
                                req, sender, now, pendingInvos >>

readResp_h == /\ pc["head"] = "readResp_h"
              /\ msgQs' = [msgQs EXCEPT ![<<head, (Find(pendingInvos_h, req_h.uniqueId))>>] = Append(@, req_h)]
              /\ pendingInvos_h' = pendingInvos_h \ {FindPair(pendingInvos_h, (req_h.uniqueId))}
              /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
              /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                              allSubmittedReadOps, terminatedYet, 
                              nonInitClients, start, timeOracle, 
                              uninitializedObjs, initObj, objs_init, obj_init, 
                              actions_init, action_init, gateway_cinit, 
                              msg_cinit, uniqueId_cinit, sentOps_init, 
                              recvdOps_init, objs, obj, actions, action, 
                              gateway_c, msg_c, uniqueId, sentOps, recvdOps, 
                              req_h, sender_h, now_h, req_t, sender_t, 
                              pendingInvos_t, now_t, req, sender, now, 
                              pendingInvos >>

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
                                timeOracle, uninitializedObjs, initObj, 
                                objs_init, obj_init, actions_init, action_init, 
                                gateway_cinit, msg_cinit, uniqueId_cinit, 
                                sentOps_init, recvdOps_init, objs, obj, 
                                actions, action, gateway_c, msg_c, uniqueId, 
                                sentOps, recvdOps, sender_h, now_h, req_t, 
                                sender_t, pendingInvos_t, now_t, req, sender, 
                                now, pendingInvos >>

respToClient == /\ pc["head"] = "respToClient"
                /\ msgQs' = [msgQs EXCEPT ![<<head, (Find(pendingInvos_h, req_h.uniqueId))>>] = Append(@, req_h)]
                /\ pendingInvos_h' = pendingInvos_h \ {FindPair(pendingInvos_h, (req_h.uniqueId))}
                /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
                /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                                allSubmittedReadOps, terminatedYet, 
                                nonInitClients, start, timeOracle, 
                                uninitializedObjs, initObj, objs_init, 
                                obj_init, actions_init, action_init, 
                                gateway_cinit, msg_cinit, uniqueId_cinit, 
                                sentOps_init, recvdOps_init, objs, obj, 
                                actions, action, gateway_c, msg_c, uniqueId, 
                                sentOps, recvdOps, req_h, sender_h, now_h, 
                                req_t, sender_t, pendingInvos_t, now_t, req, 
                                sender, now, pendingInvos >>

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
                       /\ UNCHANGED objLogs
                  ELSE /\ now_t' = timeOracle
                       /\ timeOracle' = timeOracle + 1
                       /\ objLogs' = [objLogs EXCEPT ![tail][([req_t'.op EXCEPT  !.writeCommitTs = now_t',
                                                                                 !.commitStatus = CLEAN]).obj] = Cons(([req_t'.op EXCEPT  !.writeCommitTs = now_t',
                                                                                                                                          !.commitStatus = CLEAN]), @)]
                       /\ pc' = [pc EXCEPT !["tail"] = "tailAck"]
            /\ UNCHANGED << allSubmittedWriteOps, allSubmittedReadOps, 
                            terminatedYet, nonInitClients, start, 
                            uninitializedObjs, initObj, objs_init, obj_init, 
                            actions_init, action_init, gateway_cinit, 
                            msg_cinit, uniqueId_cinit, sentOps_init, 
                            recvdOps_init, objs, obj, actions, action, 
                            gateway_c, msg_c, uniqueId, sentOps, recvdOps, 
                            req_h, sender_h, pendingInvos_h, now_h, 
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
                                  uninitializedObjs, initObj, objs_init, 
                                  obj_init, actions_init, action_init, 
                                  gateway_cinit, msg_cinit, uniqueId_cinit, 
                                  sentOps_init, recvdOps_init, objs, obj, 
                                  actions, action, gateway_c, msg_c, uniqueId, 
                                  sentOps, recvdOps, req_h, sender_h, 
                                  pendingInvos_h, now_h, sender_t, 
                                  pendingInvos_t, now_t, req, sender, now, 
                                  pendingInvos >>

tailAck == /\ pc["tail"] = "tailAck"
           /\ req_t' = [    callType |-> WRITE_RESP,
                                 uniqueId |-> req_t.uniqueId,
                                 startTs |-> req_t.startTs,
                                 commitTs |-> Read(tail, req_t.op.obj).writeCommitTs,
                                 op |-> Read(tail, req_t.op.obj)]
           /\ msgQs' = [msgQs EXCEPT ![<<tail, (Predecessors[tail])>>] = Append(@, req_t')]
           /\ pc' = [pc EXCEPT !["tail"] = "listen_t"]
           /\ UNCHANGED << objLogs, allSubmittedWriteOps, allSubmittedReadOps, 
                           terminatedYet, nonInitClients, start, timeOracle, 
                           uninitializedObjs, initObj, objs_init, obj_init, 
                           actions_init, action_init, gateway_cinit, msg_cinit, 
                           uniqueId_cinit, sentOps_init, recvdOps_init, objs, 
                           obj, actions, action, gateway_c, msg_c, uniqueId, 
                           sentOps, recvdOps, req_h, sender_h, pendingInvos_h, 
                           now_h, sender_t, pendingInvos_t, now_t, req, sender, 
                           now, pendingInvos >>

ta == listen_t \/ respFromSelf_t \/ tailAck

listen(self) == /\ pc[self] = "listen"
                /\ \E temp \in {s \in SendersTo(self) : msgQs[<<s, self>>] /= << >>}:
                     sender' = [sender EXCEPT ![self] = temp]
                /\ msgQs[<<sender'[self], self>>] /= << >>
                /\ req' = [req EXCEPT ![self] = Head(msgQs[<<sender'[self], self>>])]
                /\ msgQs' = [msgQs EXCEPT ![<<sender'[self], self>>] = Tail(@)]
                /\ IF req'[self].callType = READ_INV
                      THEN /\ IF IsDirty(self, req'[self].op.obj)
                                 THEN /\ pc' = [pc EXCEPT ![self] = "apportionQ"]
                                      /\ UNCHANGED << timeOracle, now >>
                                 ELSE /\ now' = [now EXCEPT ![self] = timeOracle]
                                      /\ timeOracle' = timeOracle + 1
                                      /\ pc' = [pc EXCEPT ![self] = "respFromSelf"]
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
                /\ UNCHANGED << allSubmittedWriteOps, allSubmittedReadOps, 
                                terminatedYet, nonInitClients, start, 
                                uninitializedObjs, initObj, objs_init, 
                                obj_init, actions_init, action_init, 
                                gateway_cinit, msg_cinit, uniqueId_cinit, 
                                sentOps_init, recvdOps_init, objs, obj, 
                                actions, action, gateway_c, msg_c, uniqueId, 
                                sentOps, recvdOps, req_h, sender_h, 
                                pendingInvos_h, now_h, req_t, sender_t, 
                                pendingInvos_t, now_t, pendingInvos >>

apportionQ(self) == /\ pc[self] = "apportionQ"
                    /\ msgQs' = [msgQs EXCEPT ![<<self, tail>>] = Append(@, req[self])]
                    /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \cup {<<(req[self].uniqueId), sender[self]>>}]
                    /\ pc' = [pc EXCEPT ![self] = "listen"]
                    /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                                    allSubmittedReadOps, terminatedYet, 
                                    nonInitClients, start, timeOracle, 
                                    uninitializedObjs, initObj, objs_init, 
                                    obj_init, actions_init, action_init, 
                                    gateway_cinit, msg_cinit, uniqueId_cinit, 
                                    sentOps_init, recvdOps_init, objs, obj, 
                                    actions, action, gateway_c, msg_c, 
                                    uniqueId, sentOps, recvdOps, req_h, 
                                    sender_h, pendingInvos_h, now_h, req_t, 
                                    sender_t, pendingInvos_t, now_t, req, 
                                    sender, now >>

respFromSelf(self) == /\ pc[self] = "respFromSelf"
                      /\ req' = [req EXCEPT ![self] =   [callType |-> READ_RESP,
                                                      uniqueId |-> req[self].uniqueId,
                                                      startTs |-> now[self],
                                                      commitTs |-> now[self],
                                                      op |-> Read(self, req[self].op.obj)]]
                      /\ msgQs' = [msgQs EXCEPT ![<<self, sender[self]>>] = Append(@, req'[self])]
                      /\ pc' = [pc EXCEPT ![self] = "listen"]
                      /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                                      allSubmittedReadOps, terminatedYet, 
                                      nonInitClients, start, timeOracle, 
                                      uninitializedObjs, initObj, objs_init, 
                                      obj_init, actions_init, action_init, 
                                      gateway_cinit, msg_cinit, uniqueId_cinit, 
                                      sentOps_init, recvdOps_init, objs, obj, 
                                      actions, action, gateway_c, msg_c, 
                                      uniqueId, sentOps, recvdOps, req_h, 
                                      sender_h, pendingInvos_h, now_h, req_t, 
                                      sender_t, pendingInvos_t, now_t, sender, 
                                      now, pendingInvos >>

fwdFromTail(self) == /\ pc[self] = "fwdFromTail"
                     /\ msgQs' = [msgQs EXCEPT ![<<self, (Find(pendingInvos[self], req[self].uniqueId))>>] = Append(@, req[self])]
                     /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \ {FindPair(pendingInvos[self], (req[self].uniqueId))}]
                     /\ pc' = [pc EXCEPT ![self] = "listen"]
                     /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                                     allSubmittedReadOps, terminatedYet, 
                                     nonInitClients, start, timeOracle, 
                                     uninitializedObjs, initObj, objs_init, 
                                     obj_init, actions_init, action_init, 
                                     gateway_cinit, msg_cinit, uniqueId_cinit, 
                                     sentOps_init, recvdOps_init, objs, obj, 
                                     actions, action, gateway_c, msg_c, 
                                     uniqueId, sentOps, recvdOps, req_h, 
                                     sender_h, pendingInvos_h, now_h, req_t, 
                                     sender_t, pendingInvos_t, now_t, req, 
                                     sender, now >>

propagate(self) == /\ pc[self] = "propagate"
                   /\ msgQs' = [msgQs EXCEPT ![<<self, (Successors[self])>>] = Append(@, req[self])]
                   /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \cup {<<(req[self].uniqueId), sender[self]>>}]
                   /\ pc' = [pc EXCEPT ![self] = "listen"]
                   /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                                   allSubmittedReadOps, terminatedYet, 
                                   nonInitClients, start, timeOracle, 
                                   uninitializedObjs, initObj, objs_init, 
                                   obj_init, actions_init, action_init, 
                                   gateway_cinit, msg_cinit, uniqueId_cinit, 
                                   sentOps_init, recvdOps_init, objs, obj, 
                                   actions, action, gateway_c, msg_c, uniqueId, 
                                   sentOps, recvdOps, req_h, sender_h, 
                                   pendingInvos_h, now_h, req_t, sender_t, 
                                   pendingInvos_t, now_t, req, sender, now >>

backProp(self) == /\ pc[self] = "backProp"
                  /\ msgQs' = [msgQs EXCEPT ![<<self, (Find(pendingInvos[self], req[self].uniqueId))>>] = Append(@, req[self])]
                  /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \ {FindPair(pendingInvos[self], (req[self].uniqueId))}]
                  /\ pc' = [pc EXCEPT ![self] = "listen"]
                  /\ UNCHANGED << objLogs, allSubmittedWriteOps, 
                                  allSubmittedReadOps, terminatedYet, 
                                  nonInitClients, start, timeOracle, 
                                  uninitializedObjs, initObj, objs_init, 
                                  obj_init, actions_init, action_init, 
                                  gateway_cinit, msg_cinit, uniqueId_cinit, 
                                  sentOps_init, recvdOps_init, objs, obj, 
                                  actions, action, gateway_c, msg_c, uniqueId, 
                                  sentOps, recvdOps, req_h, sender_h, 
                                  pendingInvos_h, now_h, req_t, sender_t, 
                                  pendingInvos_t, now_t, req, sender, now >>

n(self) == listen(self) \/ apportionQ(self) \/ respFromSelf(self)
              \/ fwdFromTail(self) \/ propagate(self) \/ backProp(self)

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
\* Last modified Sat Jun 24 23:07:18 EDT 2023 by 72jen
\* Last modified Fri Jun 23 20:02:52 EDT 2023 by jenniferlam
\* Created Tue Jun 13 12:56:59 EDT 2023 by jenniferlam
