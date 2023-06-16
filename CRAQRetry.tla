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
\* ActionType
READ == "READ"
WRITE == "WRITE"

\* CallType
READ_INV == "READ_INV" \* Read invocation
WRITE_INV == "WRITE_INV" \* Write invocation
READ_RESP == "READ_RESP" \* Read response
WRITE_RESP == "WRITE_RESP" \* Write response

\* CommitType
CLEAN == "CLEAN"
DIRTY == "DIRTY"


NullNode == CHOOSE n : n \notin Nodes

ActionType == {READ, WRITE}

CallType == {READ_INV, WRITE_INV, READ_RESP, WRITE_RESP}

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
                timeOracle = 10;
                
    \* operator definitions
    define {
        
        RECURSIVE CommitDirtyVersion(_, _) 
        CommitDirtyVersion(objLog, commitedVer) == LET mostRecentVer == Head(objLog)
                                                        uniqueId == commitedVer.uniqueId
                                                        writeCommitTs == commitedVer.writeCommitTs IN 
                                                    IF mostRecentVer.uniqueId = uniqueId THEN
                                                        Cons([mostRecentVer EXCEPT !.commitStatus = CLEAN,
                                                                                    !.writeCommitTs = writeCommitTs], 
                                                                Tail(objLog))
                                                    ELSE
                                                        Cons(mostRecentVer, 
                                                                CommitDirtyVersion(Tail(objLog), uniqueId))
        
        IsDirty(node, obj) == Head(objLogs[node][obj]).commitStatus = DIRTY
                
\*        NullReq == CHOOSE r \in RequestType: TRUE
\*        NullNode == CHOOSE n \in Nodes : TRUE
\*        NullTs == CHOOSE ts \in TimestampType : TRUE
\*        NullUniqueId == CHOOSE id \in UniqueIdType: TRUE
\*        NullCommitStatus == CHOOSE status \in CommitType : TRUE
        
        Read(node, obj) == Head(objLogs[node][obj])
        FindPair(set, k) == CHOOSE kv \in set: kv[1] = k
        Find(set, k) == LET kv == FindPair(set, k) IN kv[2]
        
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
    
    fair process(c \in Clients)
        variables   uniqueId = <<self, 1>>,
                    msg = NullReq,
                    gateway = NullNode;
    {
        clientWrite: 
        send(self, head, [  callType |-> WRITE_INV,
                            uniqueId |-> uniqueId,
                            startTs |-> NullTs,
                            commitTs |-> NullTs,
                            op |-> [obj |-> CHOOSE o \in Objects: TRUE,
                                    uniqueId |-> uniqueId,
                                    writeStartTs |-> NullTs,
                                    writeCommitTs |-> NullTs,
                                    commitStatus |-> NullCommitStatus]]);
                                    
        recvdWriteResp: with (temp \in {s \in SendersTo(self): msgQs[<<s, self>>] /= << >>}) {
            gateway := temp;
        };
        recv(gateway, self, msg); 
        assert(msg.uniqueId = uniqueId);
        assert(msg.callType = WRITE_RESP);
        addToOpSet(msg);
        
        clientReadToTail:
        uniqueId := <<self, 2>>;
        send(self, tail, [  callType |-> READ_INV,
                            uniqueId |-> uniqueId,
                            startTs |-> NullTs,
                            commitTs |-> NullTs,
                            op |-> [    obj |-> CHOOSE o \in Objects : TRUE,
                                        uniqueId |-> NullUniqueId,
                                        writeStartTs |-> NullTs,
                                        writeCommitTs |-> NullTs,
                                        commitStatus |-> NullCommitStatus]]);
                                        
        recvdReadResp: with (temp \in {node \in SendersTo(self) : msgQs[node, self] /= << >>}) {
            gateway := temp;
        }; 
        recv(gateway, self, msg);
        assert(msg.uniqueId = uniqueId);
        assert(msg.callType = READ_RESP);
        addToOpSet(msg);

        clientReadToHead:
        uniqueId := <<self, 3>>;
        send(self, head, [  callType |-> READ_INV,
                            uniqueId |-> uniqueId,
                            startTs |-> NullTs,
                            commitTs |-> NullTs,
                            op |-> [    obj |-> CHOOSE o \in Objects : TRUE,
                                        uniqueId |-> NullUniqueId,
                                        writeStartTs |-> NullTs,
                                        writeCommitTs |-> NullTs,
                                        commitStatus |-> NullCommitStatus]]);
                                        
        recvdReadRespFromHead: 
        with (temp \in {node \in SendersTo(self) : msgQs[node, self] /= << >>}) {
            gateway := temp;
        }; 
        recv(gateway, self, msg);
        assert(msg.uniqueId = uniqueId);
        assert(msg.callType = READ_RESP);
        addToOpSet(msg);
        
        concurrentWrite:
        uniqueId := <<self, 4>>;
        send(self, head, [  callType |-> WRITE_INV,
                            uniqueId |-> uniqueId,
                            startTs |-> NullTs,
                            commitTs |-> NullTs,
                            op |-> [obj |-> CHOOSE o \in Objects: TRUE,
                                    uniqueId |-> uniqueId,
                                    writeStartTs |-> NullTs,
                                    writeCommitTs |-> NullTs,
                                    commitStatus |-> NullCommitStatus]]);
        
        concurrentRead:                            
        send(self, head, [  callType |-> READ_INV,
                            uniqueId |-> <<self, 5>>,
                            startTs |-> NullTs,
                            commitTs |-> NullTs,
                            op |-> [    obj |-> CHOOSE o \in Objects: TRUE,
                                        uniqueId |-> NullUniqueId,
                                        writeStartTs |-> NullTs,
                                        writeCommitTs |-> NullTs,
                                        commitStatus |-> NullCommitStatus]]);
        waitForConcurrentWrite:
        with (temp \in {node \in SendersTo(self) : msgQs[node, self] /= << >>}) {
            gateway := temp;
        };
        recv(gateway, self, msg);
        assert(msg.callType = WRITE_RESP);
        assert(msg.uniqueId = <<self, 4>>);
        addToOpSet(msg);
        
        waitForConcurrentRead:
        with (temp \in {node \in SendersTo(self) : msgQs[node, self] /= << >>}) {
            gateway := temp;
        };
        recv(gateway, self, msg);
        assert(msg.callType = READ_RESP);
        assert(msg.uniqueId = <<self, 5>>);
        addToOpSet(msg);
        
        terminatedYet[self] := TRUE;
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
                    fwdFromTail_h: send(head, Find(pendingInvos_h, req_h.uniqueId), req_h);
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
                    respFromSelf: send(self, sender, [  callType |-> READ_RESP,
                                                        uniqueId |-> req.uniqueId,
                                                        op |-> Read(self, req.op.obj)]);
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
\* BEGIN TRANSLATION (chksum(pcal) = "e4c1885d" /\ chksum(tla) = "52fbc35d")
VARIABLES msgQs, objLogs, objTotalOrders, allSubmittedOps, terminatedYet, 
          timeOracle, pc

(* define statement *)
RECURSIVE CommitDirtyVersion(_, _)
CommitDirtyVersion(objLog, commitedVer) == LET mostRecentVer == Head(objLog)
                                                uniqueId == commitedVer.uniqueId
                                                writeCommitTs == commitedVer.writeCommitTs IN
                                            IF mostRecentVer.uniqueId = uniqueId THEN
                                                Cons([mostRecentVer EXCEPT !.commitStatus = CLEAN,
                                                                            !.writeCommitTs = writeCommitTs],
                                                        Tail(objLog))
                                            ELSE
                                                Cons(mostRecentVer,
                                                        CommitDirtyVersion(Tail(objLog), uniqueId))

IsDirty(node, obj) == Head(objLogs[node][obj]).commitStatus = DIRTY







Read(node, obj) == Head(objLogs[node][obj])
FindPair(set, k) == CHOOSE kv \in set: kv[1] = k
Find(set, k) == LET kv == FindPair(set, k) IN kv[2]

VARIABLES uniqueId, msg, gateway, req_h, sender_h, pendingInvos_h, now_h, 
          req_t, sender_t, pendingInvos_t, now_t, req, sender, pendingInvos

vars == << msgQs, objLogs, objTotalOrders, allSubmittedOps, terminatedYet, 
           timeOracle, pc, uniqueId, msg, gateway, req_h, sender_h, 
           pendingInvos_h, now_h, req_t, sender_t, pendingInvos_t, now_t, req, 
           sender, pendingInvos >>

ProcSet == (Clients) \cup {"head"} \cup {"tail"} \cup (Nodes \ {head, tail})

Init == (* Global variables *)
        /\ msgQs = [edge \in Network |-> << >>]
        /\ objLogs = [n \in Nodes |-> [o \in Objects |-> << >>]]
        /\ objTotalOrders = [ o \in Objects |-> << >> ]
        /\ allSubmittedOps = [o \in Objects |-> {}]
        /\ terminatedYet = [c \in Clients |-> FALSE]
        /\ timeOracle = 10
        (* Process c *)
        /\ uniqueId = [self \in Clients |-> <<self, 1>>]
        /\ msg = [self \in Clients |-> NullReq]
        /\ gateway = [self \in Clients |-> NullNode]
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
        /\ pendingInvos = [self \in Nodes \ {head, tail} |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "clientWrite"
                                        [] self = "head" -> "listen_h"
                                        [] self = "tail" -> "listen_t"
                                        [] self \in Nodes \ {head, tail} -> "listen"]

clientWrite(self) == /\ pc[self] = "clientWrite"
                     /\ msgQs' = [msgQs EXCEPT ![<<self, head>>] = Append(@, ([  callType |-> WRITE_INV,
                                                                                 uniqueId |-> uniqueId[self],
                                                                                 startTs |-> NullTs,
                                                                                 commitTs |-> NullTs,
                                                                                 op |-> [obj |-> CHOOSE o \in Objects: TRUE,
                                                                                         uniqueId |-> uniqueId[self],
                                                                                         writeStartTs |-> NullTs,
                                                                                         writeCommitTs |-> NullTs,
                                                                                         commitStatus |-> NullCommitStatus]]))]
                     /\ pc' = [pc EXCEPT ![self] = "recvdWriteResp"]
                     /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                                     terminatedYet, timeOracle, uniqueId, msg, 
                                     gateway, req_h, sender_h, pendingInvos_h, 
                                     now_h, req_t, sender_t, pendingInvos_t, 
                                     now_t, req, sender, pendingInvos >>

recvdWriteResp(self) == /\ pc[self] = "recvdWriteResp"
                        /\ \E temp \in {s \in SendersTo(self): msgQs[<<s, self>>] /= << >>}:
                             gateway' = [gateway EXCEPT ![self] = temp]
                        /\ msg' = [msg EXCEPT ![self] = Head(msgQs[<<gateway'[self], self>>])]
                        /\ msgQs' = [msgQs EXCEPT ![<<gateway'[self], self>>] = Tail(@)]
                        /\ Assert((msg'[self].uniqueId = uniqueId[self]), 
                                  "Failure of assertion at line 187, column 9.")
                        /\ Assert((msg'[self].callType = WRITE_RESP), 
                                  "Failure of assertion at line 188, column 9.")
                        /\ allSubmittedOps' = [allSubmittedOps EXCEPT ![msg'[self].op.obj] = allSubmittedOps[msg'[self].op.obj] \cup {msg'[self]}]
                        /\ pc' = [pc EXCEPT ![self] = "clientReadToTail"]
                        /\ UNCHANGED << objLogs, objTotalOrders, terminatedYet, 
                                        timeOracle, uniqueId, req_h, sender_h, 
                                        pendingInvos_h, now_h, req_t, sender_t, 
                                        pendingInvos_t, now_t, req, sender, 
                                        pendingInvos >>

clientReadToTail(self) == /\ pc[self] = "clientReadToTail"
                          /\ uniqueId' = [uniqueId EXCEPT ![self] = <<self, 2>>]
                          /\ msgQs' = [msgQs EXCEPT ![<<self, tail>>] = Append(@, ([  callType |-> READ_INV,
                                                                                      uniqueId |-> uniqueId'[self],
                                                                                      startTs |-> NullTs,
                                                                                      commitTs |-> NullTs,
                                                                                      op |-> [    obj |-> CHOOSE o \in Objects : TRUE,
                                                                                                  uniqueId |-> NullUniqueId,
                                                                                                  writeStartTs |-> NullTs,
                                                                                                  writeCommitTs |-> NullTs,
                                                                                                  commitStatus |-> NullCommitStatus]]))]
                          /\ pc' = [pc EXCEPT ![self] = "recvdReadResp"]
                          /\ UNCHANGED << objLogs, objTotalOrders, 
                                          allSubmittedOps, terminatedYet, 
                                          timeOracle, msg, gateway, req_h, 
                                          sender_h, pendingInvos_h, now_h, 
                                          req_t, sender_t, pendingInvos_t, 
                                          now_t, req, sender, pendingInvos >>

recvdReadResp(self) == /\ pc[self] = "recvdReadResp"
                       /\ \E temp \in {node \in SendersTo(self) : msgQs[node, self] /= << >>}:
                            gateway' = [gateway EXCEPT ![self] = temp]
                       /\ msg' = [msg EXCEPT ![self] = Head(msgQs[<<gateway'[self], self>>])]
                       /\ msgQs' = [msgQs EXCEPT ![<<gateway'[self], self>>] = Tail(@)]
                       /\ Assert((msg'[self].uniqueId = uniqueId[self]), 
                                 "Failure of assertion at line 207, column 9.")
                       /\ Assert((msg'[self].callType = READ_RESP), 
                                 "Failure of assertion at line 208, column 9.")
                       /\ allSubmittedOps' = [allSubmittedOps EXCEPT ![msg'[self].op.obj] = allSubmittedOps[msg'[self].op.obj] \cup {msg'[self]}]
                       /\ pc' = [pc EXCEPT ![self] = "clientReadToHead"]
                       /\ UNCHANGED << objLogs, objTotalOrders, terminatedYet, 
                                       timeOracle, uniqueId, req_h, sender_h, 
                                       pendingInvos_h, now_h, req_t, sender_t, 
                                       pendingInvos_t, now_t, req, sender, 
                                       pendingInvos >>

clientReadToHead(self) == /\ pc[self] = "clientReadToHead"
                          /\ uniqueId' = [uniqueId EXCEPT ![self] = <<self, 3>>]
                          /\ msgQs' = [msgQs EXCEPT ![<<self, head>>] = Append(@, ([  callType |-> READ_INV,
                                                                                      uniqueId |-> uniqueId'[self],
                                                                                      startTs |-> NullTs,
                                                                                      commitTs |-> NullTs,
                                                                                      op |-> [    obj |-> CHOOSE o \in Objects : TRUE,
                                                                                                  uniqueId |-> NullUniqueId,
                                                                                                  writeStartTs |-> NullTs,
                                                                                                  writeCommitTs |-> NullTs,
                                                                                                  commitStatus |-> NullCommitStatus]]))]
                          /\ pc' = [pc EXCEPT ![self] = "recvdReadRespFromHead"]
                          /\ UNCHANGED << objLogs, objTotalOrders, 
                                          allSubmittedOps, terminatedYet, 
                                          timeOracle, msg, gateway, req_h, 
                                          sender_h, pendingInvos_h, now_h, 
                                          req_t, sender_t, pendingInvos_t, 
                                          now_t, req, sender, pendingInvos >>

recvdReadRespFromHead(self) == /\ pc[self] = "recvdReadRespFromHead"
                               /\ \E temp \in {node \in SendersTo(self) : msgQs[node, self] /= << >>}:
                                    gateway' = [gateway EXCEPT ![self] = temp]
                               /\ msg' = [msg EXCEPT ![self] = Head(msgQs[<<gateway'[self], self>>])]
                               /\ msgQs' = [msgQs EXCEPT ![<<gateway'[self], self>>] = Tail(@)]
                               /\ Assert((msg'[self].uniqueId = uniqueId[self]), 
                                         "Failure of assertion at line 228, column 9.")
                               /\ Assert((msg'[self].callType = READ_RESP), 
                                         "Failure of assertion at line 229, column 9.")
                               /\ allSubmittedOps' = [allSubmittedOps EXCEPT ![msg'[self].op.obj] = allSubmittedOps[msg'[self].op.obj] \cup {msg'[self]}]
                               /\ pc' = [pc EXCEPT ![self] = "concurrentWrite"]
                               /\ UNCHANGED << objLogs, objTotalOrders, 
                                               terminatedYet, timeOracle, 
                                               uniqueId, req_h, sender_h, 
                                               pendingInvos_h, now_h, req_t, 
                                               sender_t, pendingInvos_t, now_t, 
                                               req, sender, pendingInvos >>

concurrentWrite(self) == /\ pc[self] = "concurrentWrite"
                         /\ uniqueId' = [uniqueId EXCEPT ![self] = <<self, 4>>]
                         /\ msgQs' = [msgQs EXCEPT ![<<self, head>>] = Append(@, ([  callType |-> WRITE_INV,
                                                                                     uniqueId |-> uniqueId'[self],
                                                                                     startTs |-> NullTs,
                                                                                     commitTs |-> NullTs,
                                                                                     op |-> [obj |-> CHOOSE o \in Objects: TRUE,
                                                                                             uniqueId |-> uniqueId'[self],
                                                                                             writeStartTs |-> NullTs,
                                                                                             writeCommitTs |-> NullTs,
                                                                                             commitStatus |-> NullCommitStatus]]))]
                         /\ pc' = [pc EXCEPT ![self] = "concurrentRead"]
                         /\ UNCHANGED << objLogs, objTotalOrders, 
                                         allSubmittedOps, terminatedYet, 
                                         timeOracle, msg, gateway, req_h, 
                                         sender_h, pendingInvos_h, now_h, 
                                         req_t, sender_t, pendingInvos_t, 
                                         now_t, req, sender, pendingInvos >>

concurrentRead(self) == /\ pc[self] = "concurrentRead"
                        /\ msgQs' = [msgQs EXCEPT ![<<self, head>>] = Append(@, ([  callType |-> READ_INV,
                                                                                    uniqueId |-> <<self, 5>>,
                                                                                    startTs |-> NullTs,
                                                                                    commitTs |-> NullTs,
                                                                                    op |-> [    obj |-> CHOOSE o \in Objects: TRUE,
                                                                                                uniqueId |-> NullUniqueId,
                                                                                                writeStartTs |-> NullTs,
                                                                                                writeCommitTs |-> NullTs,
                                                                                                commitStatus |-> NullCommitStatus]]))]
                        /\ pc' = [pc EXCEPT ![self] = "waitForConcurrentWrite"]
                        /\ UNCHANGED << objLogs, objTotalOrders, 
                                        allSubmittedOps, terminatedYet, 
                                        timeOracle, uniqueId, msg, gateway, 
                                        req_h, sender_h, pendingInvos_h, now_h, 
                                        req_t, sender_t, pendingInvos_t, now_t, 
                                        req, sender, pendingInvos >>

waitForConcurrentWrite(self) == /\ pc[self] = "waitForConcurrentWrite"
                                /\ \E temp \in {node \in SendersTo(self) : msgQs[node, self] /= << >>}:
                                     gateway' = [gateway EXCEPT ![self] = temp]
                                /\ msg' = [msg EXCEPT ![self] = Head(msgQs[<<gateway'[self], self>>])]
                                /\ msgQs' = [msgQs EXCEPT ![<<gateway'[self], self>>] = Tail(@)]
                                /\ Assert((msg'[self].callType = WRITE_RESP), 
                                          "Failure of assertion at line 259, column 9.")
                                /\ Assert((msg'[self].uniqueId = <<self, 4>>), 
                                          "Failure of assertion at line 260, column 9.")
                                /\ allSubmittedOps' = [allSubmittedOps EXCEPT ![msg'[self].op.obj] = allSubmittedOps[msg'[self].op.obj] \cup {msg'[self]}]
                                /\ pc' = [pc EXCEPT ![self] = "waitForConcurrentRead"]
                                /\ UNCHANGED << objLogs, objTotalOrders, 
                                                terminatedYet, timeOracle, 
                                                uniqueId, req_h, sender_h, 
                                                pendingInvos_h, now_h, req_t, 
                                                sender_t, pendingInvos_t, 
                                                now_t, req, sender, 
                                                pendingInvos >>

waitForConcurrentRead(self) == /\ pc[self] = "waitForConcurrentRead"
                               /\ \E temp \in {node \in SendersTo(self) : msgQs[node, self] /= << >>}:
                                    gateway' = [gateway EXCEPT ![self] = temp]
                               /\ msg' = [msg EXCEPT ![self] = Head(msgQs[<<gateway'[self], self>>])]
                               /\ msgQs' = [msgQs EXCEPT ![<<gateway'[self], self>>] = Tail(@)]
                               /\ Assert((msg'[self].callType = READ_RESP), 
                                         "Failure of assertion at line 268, column 9.")
                               /\ Assert((msg'[self].uniqueId = <<self, 5>>), 
                                         "Failure of assertion at line 269, column 9.")
                               /\ allSubmittedOps' = [allSubmittedOps EXCEPT ![msg'[self].op.obj] = allSubmittedOps[msg'[self].op.obj] \cup {msg'[self]}]
                               /\ terminatedYet' = [terminatedYet EXCEPT ![self] = TRUE]
                               /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << objLogs, objTotalOrders, 
                                               timeOracle, uniqueId, req_h, 
                                               sender_h, pendingInvos_h, now_h, 
                                               req_t, sender_t, pendingInvos_t, 
                                               now_t, req, sender, 
                                               pendingInvos >>

c(self) == clientWrite(self) \/ recvdWriteResp(self)
              \/ clientReadToTail(self) \/ recvdReadResp(self)
              \/ clientReadToHead(self) \/ recvdReadRespFromHead(self)
              \/ concurrentWrite(self) \/ concurrentRead(self)
              \/ waitForConcurrentWrite(self)
              \/ waitForConcurrentRead(self)

listen_h == /\ pc["head"] = "listen_h"
            /\ \E temp \in {s \in SendersTo(head): msgQs[<<s, head>>] /= << >>}:
                 sender_h' = temp
            /\ pc' = [pc EXCEPT !["head"] = "incomingMsg_h"]
            /\ UNCHANGED << msgQs, objLogs, objTotalOrders, allSubmittedOps, 
                            terminatedYet, timeOracle, uniqueId, msg, gateway, 
                            req_h, pendingInvos_h, now_h, req_t, sender_t, 
                            pendingInvos_t, now_t, req, sender, pendingInvos >>

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
                                  THEN /\ pc' = [pc EXCEPT !["head"] = "fwdFromTail_h"]
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
                                 terminatedYet, uniqueId, msg, gateway, 
                                 sender_h, pendingInvos_h, req_t, sender_t, 
                                 pendingInvos_t, now_t, req, sender, 
                                 pendingInvos >>

apportionQ_h == /\ pc["head"] = "apportionQ_h"
                /\ msgQs' = [msgQs EXCEPT ![<<head, tail>>] = Append(@, req_h)]
                /\ pendingInvos_h' = (pendingInvos_h \cup {<<(req_h.uniqueId), sender_h>>})
                /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
                /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                                terminatedYet, timeOracle, uniqueId, msg, 
                                gateway, req_h, sender_h, now_h, req_t, 
                                sender_t, pendingInvos_t, now_t, req, sender, 
                                pendingInvos >>

addReadTO_h == /\ pc["head"] = "addReadTO_h"
               /\ req_h' = [ callType |-> READ_RESP,
                             uniqueId |-> req_h.uniqueId,
                             startTs |-> timeOracle,
                             commitTs |-> timeOracle,
                             op |-> Read(head, req_h.op.obj)]
               /\ objTotalOrders' = [objTotalOrders EXCEPT ![req_h'.op.obj] = Cons(req_h', @)]
               /\ pc' = [pc EXCEPT !["head"] = "respFromHead"]
               /\ UNCHANGED << msgQs, objLogs, allSubmittedOps, terminatedYet, 
                               timeOracle, uniqueId, msg, gateway, sender_h, 
                               pendingInvos_h, now_h, req_t, sender_t, 
                               pendingInvos_t, now_t, req, sender, 
                               pendingInvos >>

respFromHead == /\ pc["head"] = "respFromHead"
                /\ msgQs' = [msgQs EXCEPT ![<<head, sender_h>>] = Append(@, req_h)]
                /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
                /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                                terminatedYet, timeOracle, uniqueId, msg, 
                                gateway, req_h, sender_h, pendingInvos_h, 
                                now_h, req_t, sender_t, pendingInvos_t, now_t, 
                                req, sender, pendingInvos >>

fwdFromTail_h == /\ pc["head"] = "fwdFromTail_h"
                 /\ msgQs' = [msgQs EXCEPT ![<<head, (Find(pendingInvos_h, req_h.uniqueId))>>] = Append(@, req_h)]
                 /\ pendingInvos_h' = pendingInvos_h \ {FindPair(pendingInvos_h, (req_h.uniqueId))}
                 /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
                 /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                                 terminatedYet, timeOracle, uniqueId, msg, 
                                 gateway, req_h, sender_h, now_h, req_t, 
                                 sender_t, pendingInvos_t, now_t, req, sender, 
                                 pendingInvos >>

dirtyWrite_h == /\ pc["head"] = "dirtyWrite_h"
                /\ req_h' = [req_h EXCEPT    !.startTs = now_h,
                                             !.op.writeStartTs = now_h,
                                             !.op.commitStatus = DIRTY]
                /\ objLogs' = [objLogs EXCEPT ![head][(req_h'.op).obj] = Cons((req_h'.op), @)]
                /\ pc' = [pc EXCEPT !["head"] = "propagate_h"]
                /\ UNCHANGED << msgQs, objTotalOrders, allSubmittedOps, 
                                terminatedYet, timeOracle, uniqueId, msg, 
                                gateway, sender_h, pendingInvos_h, now_h, 
                                req_t, sender_t, pendingInvos_t, now_t, req, 
                                sender, pendingInvos >>

propagate_h == /\ pc["head"] = "propagate_h"
               /\ msgQs' = [msgQs EXCEPT ![<<head, (Successors[head])>>] = Append(@, req_h)]
               /\ pendingInvos_h' = (pendingInvos_h \cup {<<(req_h.uniqueId), sender_h>>})
               /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
               /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                               terminatedYet, timeOracle, uniqueId, msg, 
                               gateway, req_h, sender_h, now_h, req_t, 
                               sender_t, pendingInvos_t, now_t, req, sender, 
                               pendingInvos >>

respToClient == /\ pc["head"] = "respToClient"
                /\ msgQs' = [msgQs EXCEPT ![<<head, (Find(pendingInvos_h, req_h.uniqueId))>>] = Append(@, req_h)]
                /\ pendingInvos_h' = pendingInvos_h \ {FindPair(pendingInvos_h, (req_h.uniqueId))}
                /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
                /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                                terminatedYet, timeOracle, uniqueId, msg, 
                                gateway, req_h, sender_h, now_h, req_t, 
                                sender_t, pendingInvos_t, now_t, req, sender, 
                                pendingInvos >>

he == listen_h \/ incomingMsg_h \/ apportionQ_h \/ addReadTO_h
         \/ respFromHead \/ fwdFromTail_h \/ dirtyWrite_h \/ propagate_h
         \/ respToClient

listen_t == /\ pc["tail"] = "listen_t"
            /\ \E temp \in {s \in SendersTo(tail) : msgQs[<<s, tail>>] /= << >>}:
                 sender_t' = temp
            /\ pc' = [pc EXCEPT !["tail"] = "incomingMsg_t"]
            /\ UNCHANGED << msgQs, objLogs, objTotalOrders, allSubmittedOps, 
                            terminatedYet, timeOracle, uniqueId, msg, gateway, 
                            req_h, sender_h, pendingInvos_h, now_h, req_t, 
                            pendingInvos_t, now_t, req, sender, pendingInvos >>

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
                                 terminatedYet, uniqueId, msg, gateway, req_h, 
                                 sender_h, pendingInvos_h, now_h, sender_t, 
                                 pendingInvos_t, req, sender, pendingInvos >>

addReadTO_t == /\ pc["tail"] = "addReadTO_t"
               /\ req_t' = [ callType |-> READ_RESP,
                             uniqueId |-> req_t.uniqueId,
                             startTs |-> now_t,
                             commitTs |-> now_t,
                             op |-> Read(tail, req_t.op.obj)]
               /\ objTotalOrders' = [objTotalOrders EXCEPT ![req_t'.op.obj] = Cons(req_t', @)]
               /\ pc' = [pc EXCEPT !["tail"] = "respFromSelf_t"]
               /\ UNCHANGED << msgQs, objLogs, allSubmittedOps, terminatedYet, 
                               timeOracle, uniqueId, msg, gateway, req_h, 
                               sender_h, pendingInvos_h, now_h, sender_t, 
                               pendingInvos_t, now_t, req, sender, 
                               pendingInvos >>

respFromSelf_t == /\ pc["tail"] = "respFromSelf_t"
                  /\ msgQs' = [msgQs EXCEPT ![<<tail, sender_t>>] = Append(@, req_t)]
                  /\ pc' = [pc EXCEPT !["tail"] = "listen_t"]
                  /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                                  terminatedYet, timeOracle, uniqueId, msg, 
                                  gateway, req_h, sender_h, pendingInvos_h, 
                                  now_h, req_t, sender_t, pendingInvos_t, 
                                  now_t, req, sender, pendingInvos >>

addWriteTO_t == /\ pc["tail"] = "addWriteTO_t"
                /\ req_t' = [    callType |-> WRITE_RESP,
                                 uniqueId |-> req_t.uniqueId,
                                 startTs |-> req_t.startTs,
                                 commitTs |-> Read(tail, req_t.op.obj).writeCommitTs,
                                 op |-> Read(tail, req_t.op.obj)]
                /\ objTotalOrders' = [objTotalOrders EXCEPT ![req_t'.op.obj] = Cons(req_t', @)]
                /\ pc' = [pc EXCEPT !["tail"] = "tailAck"]
                /\ UNCHANGED << msgQs, objLogs, allSubmittedOps, terminatedYet, 
                                timeOracle, uniqueId, msg, gateway, req_h, 
                                sender_h, pendingInvos_h, now_h, sender_t, 
                                pendingInvos_t, now_t, req, sender, 
                                pendingInvos >>

tailAck == /\ pc["tail"] = "tailAck"
           /\ msgQs' = [msgQs EXCEPT ![<<tail, (Predecessors[tail])>>] = Append(@, req_t)]
           /\ pc' = [pc EXCEPT !["tail"] = "listen_t"]
           /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                           terminatedYet, timeOracle, uniqueId, msg, gateway, 
                           req_h, sender_h, pendingInvos_h, now_h, req_t, 
                           sender_t, pendingInvos_t, now_t, req, sender, 
                           pendingInvos >>

ta == listen_t \/ incomingMsg_t \/ addReadTO_t \/ respFromSelf_t
         \/ addWriteTO_t \/ tailAck

listen(self) == /\ pc[self] = "listen"
                /\ \E temp \in {s \in SendersTo(self) : msgQs[<<s, self>>] /= << >>}:
                     sender' = [sender EXCEPT ![self] = temp]
                /\ pc' = [pc EXCEPT ![self] = "incomingMsg"]
                /\ UNCHANGED << msgQs, objLogs, objTotalOrders, 
                                allSubmittedOps, terminatedYet, timeOracle, 
                                uniqueId, msg, gateway, req_h, sender_h, 
                                pendingInvos_h, now_h, req_t, sender_t, 
                                pendingInvos_t, now_t, req, pendingInvos >>

incomingMsg(self) == /\ pc[self] = "incomingMsg"
                     /\ req' = [req EXCEPT ![self] = Head(msgQs[<<sender[self], self>>])]
                     /\ msgQs' = [msgQs EXCEPT ![<<sender[self], self>>] = Tail(@)]
                     /\ IF req'[self].callType = READ_INV
                           THEN /\ IF IsDirty(self, req'[self].op.obj)
                                      THEN /\ pc' = [pc EXCEPT ![self] = "apportionQ"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "respFromSelf"]
                                /\ UNCHANGED objLogs
                           ELSE /\ IF req'[self].callType = READ_RESP
                                      THEN /\ pc' = [pc EXCEPT ![self] = "fwdFromTail"]
                                           /\ UNCHANGED objLogs
                                      ELSE /\ IF req'[self].callType = WRITE_INV
                                                 THEN /\ objLogs' = [objLogs EXCEPT ![self][(req'[self].op).obj] = Cons((req'[self].op), @)]
                                                      /\ pc' = [pc EXCEPT ![self] = "propagate"]
                                                 ELSE /\ objLogs' = [objLogs EXCEPT ![self][req'[self].op.obj] = CommitDirtyVersion(@, req'[self].op)]
                                                      /\ pc' = [pc EXCEPT ![self] = "backProp"]
                     /\ UNCHANGED << objTotalOrders, allSubmittedOps, 
                                     terminatedYet, timeOracle, uniqueId, msg, 
                                     gateway, req_h, sender_h, pendingInvos_h, 
                                     now_h, req_t, sender_t, pendingInvos_t, 
                                     now_t, sender, pendingInvos >>

apportionQ(self) == /\ pc[self] = "apportionQ"
                    /\ msgQs' = [msgQs EXCEPT ![<<self, tail>>] = Append(@, req[self])]
                    /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \cup {<<(req[self].uniqueId), sender[self]>>}]
                    /\ pc' = [pc EXCEPT ![self] = "listen"]
                    /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                                    terminatedYet, timeOracle, uniqueId, msg, 
                                    gateway, req_h, sender_h, pendingInvos_h, 
                                    now_h, req_t, sender_t, pendingInvos_t, 
                                    now_t, req, sender >>

respFromSelf(self) == /\ pc[self] = "respFromSelf"
                      /\ msgQs' = [msgQs EXCEPT ![<<self, sender[self]>>] = Append(@, ([  callType |-> READ_RESP,
                                                                                          uniqueId |-> req[self].uniqueId,
                                                                                          op |-> Read(self, req[self].op.obj)]))]
                      /\ pc' = [pc EXCEPT ![self] = "listen"]
                      /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                                      terminatedYet, timeOracle, uniqueId, msg, 
                                      gateway, req_h, sender_h, pendingInvos_h, 
                                      now_h, req_t, sender_t, pendingInvos_t, 
                                      now_t, req, sender, pendingInvos >>

fwdFromTail(self) == /\ pc[self] = "fwdFromTail"
                     /\ msgQs' = [msgQs EXCEPT ![<<self, (Find(pendingInvos[self], req[self].uniqueId))>>] = Append(@, req[self])]
                     /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \ {FindPair(pendingInvos[self], (req[self].uniqueId))}]
                     /\ pc' = [pc EXCEPT ![self] = "listen"]
                     /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                                     terminatedYet, timeOracle, uniqueId, msg, 
                                     gateway, req_h, sender_h, pendingInvos_h, 
                                     now_h, req_t, sender_t, pendingInvos_t, 
                                     now_t, req, sender >>

propagate(self) == /\ pc[self] = "propagate"
                   /\ msgQs' = [msgQs EXCEPT ![<<self, (Successors[self])>>] = Append(@, req[self])]
                   /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \cup {<<(req[self].uniqueId), sender[self]>>}]
                   /\ pc' = [pc EXCEPT ![self] = "listen"]
                   /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                                   terminatedYet, timeOracle, uniqueId, msg, 
                                   gateway, req_h, sender_h, pendingInvos_h, 
                                   now_h, req_t, sender_t, pendingInvos_t, 
                                   now_t, req, sender >>

backProp(self) == /\ pc[self] = "backProp"
                  /\ msgQs' = [msgQs EXCEPT ![<<self, (Find(pendingInvos[self], req[self].uniqueId))>>] = Append(@, req[self])]
                  /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \ {FindPair(pendingInvos[self], (req[self].uniqueId))}]
                  /\ pc' = [pc EXCEPT ![self] = "listen"]
                  /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedOps, 
                                  terminatedYet, timeOracle, uniqueId, msg, 
                                  gateway, req_h, sender_h, pendingInvos_h, 
                                  now_h, req_t, sender_t, pendingInvos_t, 
                                  now_t, req, sender >>

n(self) == listen(self) \/ incomingMsg(self) \/ apportionQ(self)
              \/ respFromSelf(self) \/ fwdFromTail(self) \/ propagate(self)
              \/ backProp(self)

Next == he \/ ta
           \/ (\E self \in Clients: c(self))
           \/ (\E self \in Nodes \ {head, tail}: n(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in Clients : WF_vars(c(self))
        /\ WF_vars(he)
        /\ WF_vars(ta)
        /\ \A self \in Nodes \ {head, tail} : WF_vars(n(self))

\* END TRANSLATION 



GlobalTypeInvariant ==  /\ msgQs \in [Network -> {<< >>} \cup Seq(RequestType)]
                        /\ objLogs \in [Nodes -> [Objects -> {<< >>} \cup Seq(ObjectVersionType)]]
                        /\ timeOracle \in Nat

ClientTypeInvariant ==  /\ uniqueId \in [Clients -> UniqueIdType]
                        /\ msg \in [Clients -> RequestType \cup {NullReq}]
                        /\ gateway \in [Clients -> Nodes \cup {NullNode}]
                        
NodeTypeInvariant ==    /\ req \in [Nodes \ {head, tail} -> RequestType \cup {NullReq}]
                        /\ sender \in [Nodes \ {head, tail} -> Nodes \cup {NullNode}]
\*                        /\ pendingInvos \in [Nodes -> thisoneshard
                        
HeadTypeInvariant ==    /\ req_h \in RequestType \cup {NullReq}
                        /\ sender_h \in Nodes \cup Clients \cup {NullNode}
                        
TailTypeInvariant ==    /\ req_t \in RequestType \cup {NullReq}
                        /\ sender_t \in Nodes \cup Clients \cup {NullNode}

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
                                        [] OTHER -> ContainsAllOps(Tail(totalOrder), setOfOps)  \* newly commited op,
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
\* Last modified Fri Jun 16 16:33:25 EDT 2023 by 72jen
\* Last modified Thu Jun 15 15:19:09 EDT 2023 by jenniferlam
\* Created Tue Jun 13 12:56:59 EDT 2023 by jenniferlam
