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

ActionType == {READ, WRITE}

CallType == {READ_INV, WRITE_INV, READ_RESP, WRITE_RESP}

CommitType == {CLEAN, DIRTY}

TimestampType == { t: t \in 0..MaxTimestamp}
ObjectVersionType == [  obj: Objects, 
                        uniqueId: UniqueIdType, 
                        startTs: TimestampType, 
                        commitTs: TimestampType, 
                        commitStatus: CommitType]
             
RequestType == [callType: CallType, 
                uniqueId: UniqueIdType,
                op: ObjectVersionType]
PacketType == [src: Nodes, dest: Nodes, payload: RequestType] 

Cons(item, seq) == << item >> \o seq   

PendingInvoType == { <<id, node>>: id \in UniqueIdType, node \in Nodes} 
               

(****************************************************************************
--fair algorithm CRAQRetry {

    \* declaration of global algorithms
    variables   msgQs = [edge \in Network |-> << >>], \* in-order delivery via TCP
                objLogs = [n \in Nodes |-> [o \in Objects |-> << >>]],
                timeOracle = 10;
                
    \* operator definitions
    define {
        
        RECURSIVE CommitDirtyVersion(_, _) 
        CommitDirtyVersion(objLog, uniqueId) == LET mostRecentVer == Head(objLog) IN 
                                                    IF mostRecentVer.uniqueId = uniqueId THEN
                                                        Cons([mostRecentVer EXCEPT !.commitStatus = CLEAN], 
                                                                Tail(objLog))
                                                    ELSE
                                                        Cons(mostRecentVer, 
                                                                CommitDirtyVersion(Tail(objLog), uniqueId))
        
        IsDirty(node, obj) == Head(objLogs[node][obj]).commitStatus = DIRTY
        
        NullReq == CHOOSE r : r \notin RequestType
        NullNode == CHOOSE n : n \notin Nodes
        NullTs == CHOOSE ts : ts \notin TimestampType
        NullUniqueId == CHOOSE id : id \notin UniqueIdType
        NullCommitStatus == CHOOSE status : status \notin CommitType
        
        Read(node, obj) == Head(objLogs[node][obj])
        Find(set, k) == CHOOSE kv \in set: kv[1] = k
        SendersTo(n) == {\A edge \in Network: edge[2] = n}
        Now == timeOracle
        
    }
    
    \* macro definitions
    macro send(sender, receiver, msg) {
        msgQs[sender, receiver] := Append(@, msg)
    }
    
    macro recv(sender, receiver, msg) {
        when msgQs[<<sender, receiver>>] /= << >>;
        msg := Head(msgQs[sender, receiver]);
        msgQs := Tail(msgQs);
    }
    
    macro add(set, k, v) {
        set := set \cup {<<k, v>>};
    }
    
    macro remove(set, k) {
        set := @ \ {CHOOSE kv \in set : kv[1] = k};
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
    
    fair process(time="timeOracle") {
        oracle: 
        while (TRUE) {
            increment: timeOracle := timeOracle + 1;
        }
    }
    
    fair process(c \in Clients)
        variables   uniqueId = <<self, 1>>,
                    msg = NullReq,
                    gateway = NullNode,
                    null = << >>;
    {
    
        clientWrite: 
        send(self, head, [  callType |-> WRITE_INV,
                            uniqueId |-> uniqueId,
                            op |-> [obj |-> CHOOSE o \in Objects: TRUE,
                                    uniqueId |-> uniqueId,
                                    startTs |-> NullTs,
                                    commitTs |-> NullTs,
                                    commitStatus |-> NullCommitStatus]]);
                                    
        waitForIt: with (temp \in {s \in SendersTo(self): msgQs[<<s, self>>] /= << >>}) {
            gateway := temp;
        };
        recvdWriteResp: recv(gateway, self, msg); 
        assert(msg.uniqueId = uniqueId);
        assert(msg.callType = WRITE_RESP);
        
        clientRead:
        uniqueId := <<self, 2>>;
        send(self, tail, [  callType |-> READ_INV,
                            uniqueId |-> uniqueId,
                            op |-> [    obj |-> CHOOSE o \in Objects : TRUE,
                                        uniqueId |-> NullUniqueId,
                                        startTs |-> NullTs,
                                        commitTs |-> NullTs,
                                        commitStatus |-> NullCommitStatus]]);
                                        
        with (temp \in {node \in SendersTo(self) : msgQs[node, self] /= << >>}) {
            gateway := temp
        }; 
        recvdReadResp: recv(gateway, self, msg);
        assert(msg.uniqueId = uniqueId);
        assert(msg.CallType = READ_RESP);
    }
    
    fair process(n \in Nodes)
        variables   req = NullReq,
                    sender = NullNode, 
                    pendingInvos = {};
    {
        listen: while (TRUE) {
            waitForIt2: with (temp \in {s \in SendersTo(self) : msgQs[<<s, self>>] /= << >>}) {
                sender := temp;
            };
            
            incomingMsg:
            recv(sender, self, req); 
            
            readInv: 
            if (req.callType = READ_INV) {
                if (IsDirty(self, req.op.obj)) {                 
                    apportionQ: send(self, tail, req);
                    add(pendingInvos, req.uniqueId, sender);
                } else {
                    respFromSelf: send(self, sender, [  callType |-> READ_RESP,
                                                        uniqueId |-> req.uniqueId,
                                                        op |-> Read(self, req.op.obj)]);
                } 
            };             
            readResp: 
            if (req.callType = READ_RESP) {
                fwdFromTail: send(self, Find(pendingInvos, req.uniqueId), req);
                remove(pendingInvos, req.uniqueId);
            }; 
            writeInv: 
            if (req.callType = WRITE_INV) {
                if (self = tail) {
                    write(self, [req.op EXCEPT  !.commitTs = Now, 
                                                !.commitStatus = CLEAN]);
                    tailAck: send(self, Predecessors[self], [   callType |-> WRITE_RESP,
                                                                uniqueId |-> req.uniqueId,
                                                                op |-> Read(self, req.op.obj)]);   
                            
                            
                } else {
                    if (self = head) {
                        write(self, [req.op EXCEPT  !.startTs = Now, 
                                                    !.commitStatus = DIRTY]);
                    } else {
                        write(self, req.op);
                    };
                    propagate: send(self, Successors[self], req);
                    add(pendingInvos, req.uniqueId, sender);
                }
            };            
            writeResp: 
            if (req.callType = WRITE_RESP) {
                objLogs[self][req.op.obj] := CommitDirtyVersion(@, req.uniqueId);
                backProp: send(self, Find(pendingInvos, req.uniqueId), req);
                remove(pendingInvos, req.uniqueId);
            };  
        }
    }
}

****************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "98975a8a" /\ chksum(tla) = "c989005")
VARIABLES msgQs, objLogs, timeOracle, pc

(* define statement *)
RECURSIVE CommitDirtyVersion(_, _)
CommitDirtyVersion(objLog, uniqueId) == LET mostRecentVer == Head(objLog) IN
                                            IF mostRecentVer.uniqueId = uniqueId THEN
                                                Cons([mostRecentVer EXCEPT !.commitStatus = CLEAN],
                                                        Tail(objLog))
                                            ELSE
                                                Cons(mostRecentVer,
                                                        CommitDirtyVersion(Tail(objLog), uniqueId))

IsDirty(node, obj) == Head(objLogs[node][obj]).commitStatus = DIRTY

NullReq == CHOOSE r : r \notin RequestType
NullNode == CHOOSE n : n \notin Nodes
NullTs == CHOOSE ts : ts \notin TimestampType
NullUniqueId == CHOOSE id : id \notin UniqueIdType
NullCommitStatus == CHOOSE status : status \notin CommitType

Read(node, obj) == Head(objLogs[node][obj])
Find(set, k) == CHOOSE kv \in set: kv[1] = k
SendersTo(n) == {\A edge \in Network: edge[2] = n}
Now == timeOracle

VARIABLES uniqueId, msg, gateway, null, req, sender, pendingInvos

vars == << msgQs, objLogs, timeOracle, pc, uniqueId, msg, gateway, null, req, 
           sender, pendingInvos >>

ProcSet == {"timeOracle"} \cup (Clients) \cup (Nodes)

Init == (* Global variables *)
        /\ msgQs = [edge \in Network |-> << >>]
        /\ objLogs = [n \in Nodes |-> [o \in Objects |-> << >>]]
        /\ timeOracle = 10
        (* Process c *)
        /\ uniqueId = [self \in Clients |-> <<self, 1>>]
        /\ msg = [self \in Clients |-> NullReq]
        /\ gateway = [self \in Clients |-> NullNode]
        /\ null = [self \in Clients |-> << >>]
        (* Process n *)
        /\ req = [self \in Nodes |-> NullReq]
        /\ sender = [self \in Nodes |-> NullNode]
        /\ pendingInvos = [self \in Nodes |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self = "timeOracle" -> "oracle"
                                        [] self \in Clients -> "clientWrite"
                                        [] self \in Nodes -> "listen"]

oracle == /\ pc["timeOracle"] = "oracle"
          /\ pc' = [pc EXCEPT !["timeOracle"] = "increment"]
          /\ UNCHANGED << msgQs, objLogs, timeOracle, uniqueId, msg, gateway, 
                          null, req, sender, pendingInvos >>

increment == /\ pc["timeOracle"] = "increment"
             /\ timeOracle' = timeOracle + 1
             /\ pc' = [pc EXCEPT !["timeOracle"] = "oracle"]
             /\ UNCHANGED << msgQs, objLogs, uniqueId, msg, gateway, null, req, 
                             sender, pendingInvos >>

time == oracle \/ increment

clientWrite(self) == /\ pc[self] = "clientWrite"
                     /\ msgQs' = [msgQs EXCEPT ![self, head] = Append(@, ([  callType |-> WRITE_INV,
                                                                             uniqueId |-> uniqueId[self],
                                                                             op |-> [obj |-> CHOOSE o \in Objects: TRUE,
                                                                                     uniqueId |-> uniqueId[self],
                                                                                     startTs |-> NullTs,
                                                                                     commitTs |-> NullTs,
                                                                                     commitStatus |-> NullCommitStatus]]))]
                     /\ pc' = [pc EXCEPT ![self] = "waitForIt"]
                     /\ UNCHANGED << objLogs, timeOracle, uniqueId, msg, 
                                     gateway, null, req, sender, pendingInvos >>

waitForIt(self) == /\ pc[self] = "waitForIt"
                   /\ \E temp \in {s \in SendersTo(self): msgQs[<<s, self>>] /= << >>}:
                        gateway' = [gateway EXCEPT ![self] = temp]
                   /\ pc' = [pc EXCEPT ![self] = "recvdWriteResp"]
                   /\ UNCHANGED << msgQs, objLogs, timeOracle, uniqueId, msg, 
                                   null, req, sender, pendingInvos >>

recvdWriteResp(self) == /\ pc[self] = "recvdWriteResp"
                        /\ msgQs[<<gateway[self], self>>] /= << >>
                        /\ msg' = [msg EXCEPT ![self] = Head(msgQs[gateway[self], self])]
                        /\ msgQs' = Tail(msgQs)
                        /\ Assert((msg'[self].uniqueId = uniqueId[self]), 
                                  "Failure of assertion at line 168, column 9.")
                        /\ Assert((msg'[self].callType = WRITE_RESP), 
                                  "Failure of assertion at line 169, column 9.")
                        /\ pc' = [pc EXCEPT ![self] = "clientRead"]
                        /\ UNCHANGED << objLogs, timeOracle, uniqueId, gateway, 
                                        null, req, sender, pendingInvos >>

clientRead(self) == /\ pc[self] = "clientRead"
                    /\ uniqueId' = [uniqueId EXCEPT ![self] = <<self, 2>>]
                    /\ msgQs' = [msgQs EXCEPT ![self, tail] = Append(@, ([  callType |-> READ_INV,
                                                                            uniqueId |-> uniqueId'[self],
                                                                            op |-> [    obj |-> CHOOSE o \in Objects : TRUE,
                                                                                        uniqueId |-> NullUniqueId,
                                                                                        startTs |-> NullTs,
                                                                                        commitTs |-> NullTs,
                                                                                        commitStatus |-> NullCommitStatus]]))]
                    /\ \E temp \in {node \in SendersTo(self) : msgQs'[node, self] /= << >>}:
                         gateway' = [gateway EXCEPT ![self] = temp]
                    /\ pc' = [pc EXCEPT ![self] = "recvdReadResp"]
                    /\ UNCHANGED << objLogs, timeOracle, msg, null, req, 
                                    sender, pendingInvos >>

recvdReadResp(self) == /\ pc[self] = "recvdReadResp"
                       /\ msgQs[<<gateway[self], self>>] /= << >>
                       /\ msg' = [msg EXCEPT ![self] = Head(msgQs[gateway[self], self])]
                       /\ msgQs' = Tail(msgQs)
                       /\ Assert((msg'[self].uniqueId = uniqueId[self]), 
                                 "Failure of assertion at line 185, column 9.")
                       /\ Assert((msg'[self].CallType = READ_RESP), 
                                 "Failure of assertion at line 186, column 9.")
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << objLogs, timeOracle, uniqueId, gateway, 
                                       null, req, sender, pendingInvos >>

c(self) == clientWrite(self) \/ waitForIt(self) \/ recvdWriteResp(self)
              \/ clientRead(self) \/ recvdReadResp(self)

listen(self) == /\ pc[self] = "listen"
                /\ pc' = [pc EXCEPT ![self] = "waitForIt2"]
                /\ UNCHANGED << msgQs, objLogs, timeOracle, uniqueId, msg, 
                                gateway, null, req, sender, pendingInvos >>

waitForIt2(self) == /\ pc[self] = "waitForIt2"
                    /\ \E temp \in {s \in SendersTo(self) : msgQs[<<s, self>>] /= << >>}:
                         sender' = [sender EXCEPT ![self] = temp]
                    /\ pc' = [pc EXCEPT ![self] = "incomingMsg"]
                    /\ UNCHANGED << msgQs, objLogs, timeOracle, uniqueId, msg, 
                                    gateway, null, req, pendingInvos >>

incomingMsg(self) == /\ pc[self] = "incomingMsg"
                     /\ msgQs[<<sender[self], self>>] /= << >>
                     /\ req' = [req EXCEPT ![self] = Head(msgQs[sender[self], self])]
                     /\ msgQs' = Tail(msgQs)
                     /\ pc' = [pc EXCEPT ![self] = "readInv"]
                     /\ UNCHANGED << objLogs, timeOracle, uniqueId, msg, 
                                     gateway, null, sender, pendingInvos >>

readInv(self) == /\ pc[self] = "readInv"
                 /\ IF req[self].callType = READ_INV
                       THEN /\ IF IsDirty(self, req[self].op.obj)
                                  THEN /\ pc' = [pc EXCEPT ![self] = "apportionQ"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "respFromSelf"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "readResp"]
                 /\ UNCHANGED << msgQs, objLogs, timeOracle, uniqueId, msg, 
                                 gateway, null, req, sender, pendingInvos >>

apportionQ(self) == /\ pc[self] = "apportionQ"
                    /\ msgQs' = [msgQs EXCEPT ![self, tail] = Append(@, req[self])]
                    /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \cup {<<(req[self].uniqueId), sender[self]>>}]
                    /\ pc' = [pc EXCEPT ![self] = "readResp"]
                    /\ UNCHANGED << objLogs, timeOracle, uniqueId, msg, 
                                    gateway, null, req, sender >>

respFromSelf(self) == /\ pc[self] = "respFromSelf"
                      /\ msgQs' = [msgQs EXCEPT ![self, sender[self]] = Append(@, ([  callType |-> READ_RESP,
                                                                                      uniqueId |-> req[self].uniqueId,
                                                                                      op |-> Read(self, req[self].op.obj)]))]
                      /\ pc' = [pc EXCEPT ![self] = "readResp"]
                      /\ UNCHANGED << objLogs, timeOracle, uniqueId, msg, 
                                      gateway, null, req, sender, pendingInvos >>

readResp(self) == /\ pc[self] = "readResp"
                  /\ IF req[self].callType = READ_RESP
                        THEN /\ pc' = [pc EXCEPT ![self] = "fwdFromTail"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "writeInv"]
                  /\ UNCHANGED << msgQs, objLogs, timeOracle, uniqueId, msg, 
                                  gateway, null, req, sender, pendingInvos >>

fwdFromTail(self) == /\ pc[self] = "fwdFromTail"
                     /\ msgQs' = [msgQs EXCEPT ![self, (Find(pendingInvos[self], req[self].uniqueId))] = Append(@, req[self])]
                     /\ pendingInvos' = [pendingInvos EXCEPT ![self] = @ \ {CHOOSE kv \in pendingInvos[self] : kv[1] = (req[self].uniqueId)}]
                     /\ pc' = [pc EXCEPT ![self] = "writeInv"]
                     /\ UNCHANGED << objLogs, timeOracle, uniqueId, msg, 
                                     gateway, null, req, sender >>

writeInv(self) == /\ pc[self] = "writeInv"
                  /\ IF req[self].callType = WRITE_INV
                        THEN /\ IF self = tail
                                   THEN /\ objLogs' = [objLogs EXCEPT ![self][([req[self].op EXCEPT  !.commitTs = Now,
                                                                                                     !.commitStatus = CLEAN]).obj] = Cons(([req[self].op EXCEPT  !.commitTs = Now,
                                                                                                                                                                 !.commitStatus = CLEAN]), @)]
                                        /\ pc' = [pc EXCEPT ![self] = "tailAck"]
                                   ELSE /\ IF self = head
                                              THEN /\ objLogs' = [objLogs EXCEPT ![self][([req[self].op EXCEPT  !.startTs = Now,
                                                                                                                !.commitStatus = DIRTY]).obj] = Cons(([req[self].op EXCEPT  !.startTs = Now,
                                                                                                                                                                            !.commitStatus = DIRTY]), @)]
                                              ELSE /\ objLogs' = [objLogs EXCEPT ![self][(req[self].op).obj] = Cons((req[self].op), @)]
                                        /\ pc' = [pc EXCEPT ![self] = "propagate"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "writeResp"]
                             /\ UNCHANGED objLogs
                  /\ UNCHANGED << msgQs, timeOracle, uniqueId, msg, gateway, 
                                  null, req, sender, pendingInvos >>

tailAck(self) == /\ pc[self] = "tailAck"
                 /\ msgQs' = [msgQs EXCEPT ![self, (Predecessors[self])] = Append(@, ([   callType |-> WRITE_RESP,
                                                                                          uniqueId |-> req[self].uniqueId,
                                                                                          op |-> Read(self, req[self].op.obj)]))]
                 /\ pc' = [pc EXCEPT ![self] = "writeResp"]
                 /\ UNCHANGED << objLogs, timeOracle, uniqueId, msg, gateway, 
                                 null, req, sender, pendingInvos >>

propagate(self) == /\ pc[self] = "propagate"
                   /\ msgQs' = [msgQs EXCEPT ![self, (Successors[self])] = Append(@, req[self])]
                   /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \cup {<<(req[self].uniqueId), sender[self]>>}]
                   /\ pc' = [pc EXCEPT ![self] = "writeResp"]
                   /\ UNCHANGED << objLogs, timeOracle, uniqueId, msg, gateway, 
                                   null, req, sender >>

writeResp(self) == /\ pc[self] = "writeResp"
                   /\ IF req[self].callType = WRITE_RESP
                         THEN /\ objLogs' = [objLogs EXCEPT ![self][req[self].op.obj] = CommitDirtyVersion(@, req[self].uniqueId)]
                              /\ pc' = [pc EXCEPT ![self] = "backProp"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "listen"]
                              /\ UNCHANGED objLogs
                   /\ UNCHANGED << msgQs, timeOracle, uniqueId, msg, gateway, 
                                   null, req, sender, pendingInvos >>

backProp(self) == /\ pc[self] = "backProp"
                  /\ msgQs' = [msgQs EXCEPT ![self, (Find(pendingInvos[self], req[self].uniqueId))] = Append(@, req[self])]
                  /\ pendingInvos' = [pendingInvos EXCEPT ![self] = @ \ {CHOOSE kv \in pendingInvos[self] : kv[1] = (req[self].uniqueId)}]
                  /\ pc' = [pc EXCEPT ![self] = "listen"]
                  /\ UNCHANGED << objLogs, timeOracle, uniqueId, msg, gateway, 
                                  null, req, sender >>

n(self) == listen(self) \/ waitForIt2(self) \/ incomingMsg(self)
              \/ readInv(self) \/ apportionQ(self) \/ respFromSelf(self)
              \/ readResp(self) \/ fwdFromTail(self) \/ writeInv(self)
              \/ tailAck(self) \/ propagate(self) \/ writeResp(self)
              \/ backProp(self)

Next == time
           \/ (\E self \in Clients: c(self))
           \/ (\E self \in Nodes: n(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ WF_vars(time)
        /\ \A self \in Clients : WF_vars(c(self))
        /\ \A self \in Nodes : WF_vars(n(self))

\* END TRANSLATION 

TypeInvariant == TRUE
\*TypeInvariant ==    /\ msgQs \in [Network -> {<< >>} \cup Seq(RequestType)]
\*                    /\ objLogs \in [Nodes -> [Objects -> {<< >>} \cup Seq(ObjectVersionType)]]
\*                    /\ timeOracle \in 1..MaxTimestamp
\*                    /\ uniqueId \in [Clients -> UniqueIdType]
\*                    /\ msg \in [Clients -> RequestType \cup {NullReq}]
\*                    /\ gateway \in [Clients -> Nodes \cup {NullNode}] 
\*                    /\ req \in [Nodes -> RequestType \cup {NullReq}]
\*                    /\ sender \in [Nodes -> Nodes \cup {NullNode}]
\*                    /\ pendingInvos \in [Nodes -> thisoneshard


=============================================================================
\* Modification History
\* Last modified Wed Jun 14 16:32:20 EDT 2023 by jenniferlam
\* Created Tue Jun 13 12:56:59 EDT 2023 by jenniferlam
