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

UniqueIds == {<<c, id>> : c \in Clients, id \in 0..NumMsgs}

ASSUME  /\ head \in Nodes
        /\ tail \in Nodes
        /\ Cardinality(Nodes) >= 2
        /\ Cardinality(Edges) = Cardinality(Nodes \ {head}) * 2 + Cardinality(Nodes \ {tail}) * 2 - 2
        /\ Edges \subseteq Network
        /\ ClientEdges \subseteq Network
        /\ Cardinality(UniqueIds) = Cardinality(Clients) * (NumMsgs + 1)
        
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
COMMITTED == "COMMITTED"
DIRTY == "DIRTY"

ActionType == {READ, WRITE}

CallType == {READ_INV, WRITE_INV, READ_RESP, WRITE_RESP}

CommitType == {COMMITTED, DIRTY}

TimestampType == { t: t \in 0..MaxTimestamp}
UniqueIdType == { <<c, i>> : c \in Clients, i \in NumMsgs}
ObjectVersionType == [  obj: Objects, 
                        uniqueId: UniqueIdType, 
                        startTs: TimestampType, 
                        commitTs: TimestampType, 
                        commitStatus: CommitType]
             
RequestType == [callType: CallType, 
                uniqueId: UniqueIdType,
                op: ObjectVersionType]
PacketType == [src: Nodes, dest: Nodes, payload: RequestType]     
               

(****************************************************************************
--fair algorithm CRAQRetry {

    \* declaration of global algorithms
    variables   qs = [n \in Nodes |-> << >>],
                objLogs = [n \in Nodes |-> [o \in Objects |-> << >>]];
                
    \* operator definitions
    define {
        
        IsDirty(node, obj) == Head(objLogs[node][obj]).commitStatus = DIRTY
        
        defaultReq == CHOOSE r \in RequestType: TRUE
        defaultNode == CHOOSE n \in Nodes : TRUE
        defaultUniqueId == CHOOSE u \in UniqueIdType : TRUE
        
        Read(self, obj) == Head(objLogs[node][obj])
        Find(set, k) == CHOOSE kv \in set: kv[1] = k
        
    }
    
    \* macro definitions
    macro send(sender, receiver, msg) {
        qs[src] := Append(@, [  src |-> sender, 
                                dest |-> receiver,
                                payload |-> msg]); \* append packet
    }
    
    macro recv(sender, receiver, msg) {
        sender := Head(qs[receiver]).src;   \* set sender
        msg := Head(qs[receiver]).payload;  \* set payload
        qs[receiver] := Tail(@);            \* dequeue head
    }
    
    macro add(set, k, v) {
        set := @ \cup {<<k, v>>};
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
    
    
  
    fair process(n \in Nodes \ {head, tail})
        variables   req = defaultReq,
                    sender = defaultNode, 
                    pendingInvos = {};
    {
    
        listen: while (TRUE) {
            when qs[self] /= << >>;
            
            incomingMsg: recv(sender, self, req);
            add(pendingInvos, req.uniqueId, sender); 
            
            if (req.callType = READ_INV) {
                if (IsDirty(self, req.obj)) {
                    \* apportion query                    
                    send(self, tail, req);
                } else {
                    \* respond with this version
                    send(self, sender, [callType |-> READ_RESP,
                                        uniqueId |-> req.uniqueId,
                                        op |-> Read(self, req.obj)]);
                    remove(pendingInvos, req.uniqueId);
                }
            };                 
            if (req.callType = READ_RESP) {
                send(self, Find(pendingInvos, req.uniqueId), req);
                remove(pendingInvos, req.uniqueId);
            };
            if (req.callType = WRITE_INV) {
                
            }    
            
        }
    }
}


****************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "c25e549d" /\ chksum(tla) = "a063eb28")
VARIABLES qs, objLogs, pc

(* define statement *)
isDirty(node, obj) == Head(objLogs[node][obj]).isDirty

defaultReq == CHOOSE r \in RequestType: TRUE
defaultNode == CHOOSE n \in Nodes : TRUE
defaultUniqueId == CHOOSE u \in UniqueIdType : TRUE

VARIABLES req, sender, pendingInvos

vars == << qs, objLogs, pc, req, sender, pendingInvos >>

ProcSet == (Nodes \ {head, tail})

Init == (* Global variables *)
        /\ qs = [n \in Nodes |-> << >>]
        /\ objLogs = [n \in Nodes |-> [o \in Objects |-> << >>]]
        (* Process n *)
        /\ req = [self \in Nodes \ {head, tail} |-> defaultReq]
        /\ sender = [self \in Nodes \ {head, tail} |-> defaultNode]
        /\ pendingInvos = [self \in Nodes \ {head, tail} |-> {}]
        /\ pc = [self \in ProcSet |-> "listen"]

listen(self) == /\ pc[self] = "listen"
                /\ qs[self] /= << >>
                /\ pc' = [pc EXCEPT ![self] = "incomingReq"]
                /\ UNCHANGED << qs, objLogs, req, sender, pendingInvos >>

incomingReq(self) == /\ pc[self] = "incomingReq"
                     /\ sender' = [sender EXCEPT ![self] = Head(qs[self]).src]
                     /\ req' = [req EXCEPT ![self] = Head(qs[self]).payload]
                     /\ qs' = [qs EXCEPT ![self] = Tail(@)]
                     /\ pendingInvos' = [pendingInvos EXCEPT ![self] = @ \cup {<<(req'[self].uniqueId), sender'[self]>>}]
                     /\ pc' = [pc EXCEPT ![self] = "listen"]
                     /\ UNCHANGED objLogs

n(self) == listen(self) \/ incomingReq(self)

Next == (\E self \in Nodes \ {head, tail}: n(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in Nodes \ {head, tail} : WF_vars(n(self))

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Tue Jun 13 17:34:46 EDT 2023 by jenniferlam
\* Created Tue Jun 13 12:56:59 EDT 2023 by jenniferlam
