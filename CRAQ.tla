-------------------------------- MODULE CRAQ --------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Clients, Nodes, head, tail, NumMsgs, Objects, nullObj

RECURSIVE FormChainTopology(_,_)
FormChainTopology(curr, nodes) ==   IF nodes = {} THEN {} 
                                    ELSE LET n == CHOOSE node \in nodes : TRUE
                                         IN  {<<curr, n>>} \cup FormChainTopology(n, nodes \ {n})
                                            
NextEdges == FormChainTopology(head, Nodes \ {head})
PrevEdges == { <<e[2], e[1]>> : e \in NextEdges } 

Descendants == [n \in Nodes \ {tail} |-> LET e == CHOOSE edge \in NextEdges : edge[1] = n IN e[2]]
Ancestors == [n \in Nodes \ {head} |-> LET e == CHOOSE edge \in PrevEdges : edge[1] = n IN e[2]]

EdgesToTail == { <<n, tail>> : n \in Nodes \ {tail}}
EdgesFromTail == { <<tail, n>> : n \in Nodes \ {tail}}
Edges == NextEdges \cup PrevEdges \cup EdgesToTail \cup EdgesFromTail

EdgesFromClients == { <<c, n>> : c \in Clients, n \in Nodes}
EdgesToClients == { <<n, c>> : c \in Clients, n \in Nodes }
ClientEdges == EdgesFromClients \cup EdgesToClients

Network == Edges \cup ClientEdges

ASSUME  /\ head \in Nodes
        /\ tail \in Nodes
        /\ Cardinality(Nodes) >= 2
        /\ Cardinality(Edges) = Cardinality(Nodes \ {head}) * 2 + Cardinality(Nodes \ {tail}) * 2
        /\ Cardinality(Descendants) = Cardinality(Nodes \ {head})
        /\ Cardinality(Ancestors) = Cardinality(Nodes \ {tail})
        /\ Edges \subseteq Network
        /\ ClientEdges \subseteq Network
-----------------------------------------------------------------------------

READ == TRUE
WRITE == ~READ
Actions == {READ, WRITE}

NULLOP == [ obj |-> CHOOSE o \in Objects: TRUE,
            uniqueId |-> CHOOSE i \in Int : TRUE,
            action |-> CHOOSE a \in Actions : TRUE]
            
NULLLOGENTRY == [   uniqueId |-> CHOOSE i \in Int : TRUE,
                    isDirty |-> CHOOSE b \in {TRUE, FALSE} : TRUE]

\* LogEntry == [uniqueId (int), isDirty (bool) ]
\* Operation == [obj (Object), uniqueId (int), action (Action)]

(****************************************************************************

--fair algorithm CRAQ {

        \* declaration of global variables
        variables   msgQs = [e \in Network |-> << >>];
        
        \* operator definitions
        define {
            
            PotentialRequestClients(n) == IF n = head THEN Clients ELSE {Ancestors[n]} \cup Clients

            readObjFromSelf(objLogs, obj) == [  obj |-> obj, 
                                                uniqueId |-> Head(objLogs[obj]).uniqueId, 
                                                action |-> WRITE]
            isDirtyVersion(objLogs, obj) == Head(objLogs[obj]).isDirty
        }
        
        \* macro definitions
        macro send(edge, msg) {
            msgQs[edge] := Append(@, msg);
        }
        macro rcv(edge, resp) {
            await msgQs[edge] /= << >>;
            resp := Head(msgQs[edge]);
            msgQs[edge] := Tail(@);
        }
        macro dirtyWriteObj(objLogs, obj) {
            objLogs[obj] := Append(@, [uniqueId |-> op.uniqueId, isDirty |-> TRUE]);
        }
        
        \* procedures
        procedure apportionQuery(src, op, resp) {
            sendQuery: send(<<src, tail>>, op);
            rcvResp: rcv(<<tail, src>>, resp); 
        }
    
    \* algorithm body or process declarations  
    
    
    \* Every client will simply send three write operations to every object
    \* to the head.                  
    fair process(client \in Clients) 
        variables   sequencer = 1,
                    objects = Objects,
                    obj;
    {
        newMsg: while (sequencer <= 3) {
            newObj: while (objects /= {}) {
                obj := CHOOSE o \in objects : TRUE; 
                send(<<self, head>>, [  obj |-> obj, 
                                        uniqueId |-> <<self, sequencer>>, 
                                        action |-> WRITE]);
                objects := objects \ {obj};
            };
            
            increment: sequencer := @ + 1;
        }
    }

    fair process (headProcess="head") 
        variables   next = Descendants[head],
                    objLogs = [o \in Objects |-> << >>],
                    op, resp, client; 
    {
        listen: 
        while (TRUE) {
        
            client := \E c \in PotentialRequestClients(head): msgQs[<<c, head>>] /= << >>;
                                                       
            incomingClientReq: 
            rcv(<<client, head>>, op); 
            if (op.action = READ) {
            
                readingOjb: if (isDirtyVersion(objLogs, op.obj)) {
                    call apportionQuery(head, op, resp);
                } else {    
                    resp := readObjFromSelf(objLogs, op.obj);
                };
                
                respondToClient: send(<<head, client>>, resp);
                
            } else {
                    
                dirtyWrite: dirtyWriteObj(objLogs, op.obj);
                    
                propagate: send(<<head, next>>, op);
                    
                recvAck: rcv(<<next, head>>, resp);
                    
                applyWrite: objLogs[op.obj].isDirty := FALSE;
                                 
                ackSuccessfulWrite: resp := [  obj |-> op.obj,
                                                uniqueId |-> op.uniqueId,
                                                action |-> TRUE];
                send(<<head, client>>, resp);                                        
            }
        }
    }
    
    fair process (tailProcess="tail") 
        variables   prev = Ancestors[tail],
                    objLogs = [o \in Objects |-> << >>],
                    op, resp, requester;
    {
        listen: while (TRUE) {
            requester := \E n \in PotentialRequestClients(tail) : msgQs[<<n, tail>>] /= << >>;
            
            incomingReq:
            rcv(<<requester, tail>>, op);
            if (op.action = READ) {
                readObj: resp := readObjFromSelf(objLogs, op.obj); 
                
                respond: send(<<tail, requester>>, resp);
                 
            } else {
            
                applyWrite: objLogs[op.obj] := Append(objLogs[op.obj], [uniqueId |-> op.uniqueId, isDirty |-> FALSE]);
                                 
                ackSuccessfulWrite: resp := [  obj |-> op.obj,
                                                uniqueId |-> op.uniqueId,
                                                action |-> TRUE];
                send(<<tail, requester>>, resp);     
            } 
        }
    }
    
    fair process (n \in Nodes \ {head, tail})
        variables   prev = Ancestors[self],
                    next = Descendants[self],
                    objLogs = [o \in Objects |-> << >>],
                    op, resp, requester; 
    {
        listen: while (TRUE) {
            requester := \E n \in PotentialRequestClients(self) : msgQs[<<n, self>>] /= << >>;
            
            incomingReq: 
            rcv(<<requester, self>>, op); 
            if (op.action = READ) {
            
                readingOjb: if (isDirtyVersion(objLogs, op.obj)) {
                    call apportionQuery(self, op, resp);
                } else {    
                    resp := readObjFromSelf(objLogs, op.obj);
                };
                
                respondToClient: send(<<self, requester>>, resp);
            } else {
                dirtyWrite: dirtyWriteObj(objLogs, op.obj);
                    
                propagate: send(<<self, next>>, op);
                    
                recvAck: rcv(<<prev, head>>, resp);
                    
                applyWrite: objLogs[op.obj].isDirty := FALSE;
                                 
                ackSuccessfulWrite: resp := [   obj |-> op.obj,
                                                uniqueId |-> op.uniqueId,
                                                action |-> TRUE];
                send(<<self, prev>>, resp); 
            }
        }  
    }
}
****************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "d237e98" /\ chksum(tla) = "8d0f7a03")
\* Label listen of process headProcess at line 117 col 9 changed to listen_
\* Label readingOjb of process headProcess at line 125 col 29 changed to readingOjb_
\* Label respondToClient of process headProcess at line 71 col 13 changed to respondToClient_
\* Label dirtyWrite of process headProcess at line 79 col 13 changed to dirtyWrite_
\* Label propagate of process headProcess at line 71 col 13 changed to propagate_
\* Label recvAck of process headProcess at line 74 col 13 changed to recvAck_
\* Label applyWrite of process headProcess at line 141 col 29 changed to applyWrite_
\* Label ackSuccessfulWrite of process headProcess at line 143 col 37 changed to ackSuccessfulWrite_
\* Label listen of process tailProcess at line 156 col 17 changed to listen_t
\* Label incomingReq of process tailProcess at line 74 col 13 changed to incomingReq_
\* Label applyWrite of process tailProcess at line 168 col 29 changed to applyWrite_t
\* Label ackSuccessfulWrite of process tailProcess at line 170 col 37 changed to ackSuccessfulWrite_t
\* Process client at line 93 col 10 changed to client_
\* Process variable next of process headProcess at line 112 col 21 changed to next_
\* Process variable objLogs of process headProcess at line 113 col 21 changed to objLogs_
\* Process variable op of process headProcess at line 114 col 21 changed to op_
\* Process variable resp of process headProcess at line 114 col 25 changed to resp_
\* Process variable prev of process tailProcess at line 152 col 21 changed to prev_
\* Process variable objLogs of process tailProcess at line 153 col 21 changed to objLogs_t
\* Process variable op of process tailProcess at line 154 col 21 changed to op_t
\* Process variable resp of process tailProcess at line 154 col 25 changed to resp_t
\* Process variable requester of process tailProcess at line 154 col 31 changed to requester_
\* Process variable op of process n at line 182 col 21 changed to op_n
\* Process variable resp of process n at line 182 col 25 changed to resp_n
CONSTANT defaultInitValue
VARIABLES msgQs, pc, stack

(* define statement *)
PotentialRequestClients(n) == IF n = head THEN Clients ELSE {Ancestors[n]} \cup Clients

readObjFromSelf(objLogs, obj) == [  obj |-> obj,
                                    uniqueId |-> Head(objLogs[obj]).uniqueId,
                                    action |-> WRITE]
isDirtyVersion(objLogs, obj) == Head(objLogs[obj]).isDirty

VARIABLES src, op, resp, sequencer, objects, obj, next_, objLogs_, op_, resp_, 
          client, prev_, objLogs_t, op_t, resp_t, requester_, prev, next, 
          objLogs, op_n, resp_n, requester

vars == << msgQs, pc, stack, src, op, resp, sequencer, objects, obj, next_, 
           objLogs_, op_, resp_, client, prev_, objLogs_t, op_t, resp_t, 
           requester_, prev, next, objLogs, op_n, resp_n, requester >>

ProcSet == (Clients) \cup {"head"} \cup {"tail"} \cup (Nodes \ {head, tail})

Init == (* Global variables *)
        /\ msgQs = [e \in Network |-> << >>]
        (* Procedure apportionQuery *)
        /\ src = [ self \in ProcSet |-> defaultInitValue]
        /\ op = [ self \in ProcSet |-> defaultInitValue]
        /\ resp = [ self \in ProcSet |-> defaultInitValue]
        (* Process client_ *)
        /\ sequencer = [self \in Clients |-> 1]
        /\ objects = [self \in Clients |-> Objects]
        /\ obj = [self \in Clients |-> defaultInitValue]
        (* Process headProcess *)
        /\ next_ = Descendants[head]
        /\ objLogs_ = [o \in Objects |-> << >>]
        /\ op_ = defaultInitValue
        /\ resp_ = defaultInitValue
        /\ client = defaultInitValue
        (* Process tailProcess *)
        /\ prev_ = Ancestors[tail]
        /\ objLogs_t = [o \in Objects |-> << >>]
        /\ op_t = defaultInitValue
        /\ resp_t = defaultInitValue
        /\ requester_ = defaultInitValue
        (* Process n *)
        /\ prev = [self \in Nodes \ {head, tail} |-> Ancestors[self]]
        /\ next = [self \in Nodes \ {head, tail} |-> Descendants[self]]
        /\ objLogs = [self \in Nodes \ {head, tail} |-> [o \in Objects |-> << >>]]
        /\ op_n = [self \in Nodes \ {head, tail} |-> defaultInitValue]
        /\ resp_n = [self \in Nodes \ {head, tail} |-> defaultInitValue]
        /\ requester = [self \in Nodes \ {head, tail} |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "newMsg"
                                        [] self = "head" -> "listen_"
                                        [] self = "tail" -> "listen_t"
                                        [] self \in Nodes \ {head, tail} -> "listen"]

sendQuery(self) == /\ pc[self] = "sendQuery"
                   /\ msgQs' = [msgQs EXCEPT ![(<<src[self], tail>>)] = Append(@, op[self])]
                   /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                   /\ UNCHANGED << stack, src, op, resp, sequencer, objects, 
                                   obj, next_, objLogs_, op_, resp_, client, 
                                   prev_, objLogs_t, op_t, resp_t, requester_, 
                                   prev, next, objLogs, op_n, resp_n, 
                                   requester >>

rcvResp(self) == /\ pc[self] = "rcvResp"
                 /\ msgQs[(<<tail, src[self]>>)] /= << >>
                 /\ resp' = [resp EXCEPT ![self] = Head(msgQs[(<<tail, src[self]>>)])]
                 /\ msgQs' = [msgQs EXCEPT ![(<<tail, src[self]>>)] = Tail(@)]
                 /\ pc' = [pc EXCEPT ![self] = "Error"]
                 /\ UNCHANGED << stack, src, op, sequencer, objects, obj, 
                                 next_, objLogs_, op_, resp_, client, prev_, 
                                 objLogs_t, op_t, resp_t, requester_, prev, 
                                 next, objLogs, op_n, resp_n, requester >>

apportionQuery(self) == sendQuery(self) \/ rcvResp(self)

newMsg(self) == /\ pc[self] = "newMsg"
                /\ IF sequencer[self] <= 3
                      THEN /\ pc' = [pc EXCEPT ![self] = "newObj"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << msgQs, stack, src, op, resp, sequencer, 
                                objects, obj, next_, objLogs_, op_, resp_, 
                                client, prev_, objLogs_t, op_t, resp_t, 
                                requester_, prev, next, objLogs, op_n, resp_n, 
                                requester >>

newObj(self) == /\ pc[self] = "newObj"
                /\ IF objects[self] /= {}
                      THEN /\ obj' = [obj EXCEPT ![self] = CHOOSE o \in objects[self] : TRUE]
                           /\ msgQs' = [msgQs EXCEPT ![(<<self, head>>)] = Append(@, ([  obj |-> obj'[self],
                                                                                         uniqueId |-> <<self, sequencer[self]>>,
                                                                                         action |-> WRITE]))]
                           /\ objects' = [objects EXCEPT ![self] = objects[self] \ {obj'[self]}]
                           /\ pc' = [pc EXCEPT ![self] = "newObj"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "increment"]
                           /\ UNCHANGED << msgQs, objects, obj >>
                /\ UNCHANGED << stack, src, op, resp, sequencer, next_, 
                                objLogs_, op_, resp_, client, prev_, objLogs_t, 
                                op_t, resp_t, requester_, prev, next, objLogs, 
                                op_n, resp_n, requester >>

increment(self) == /\ pc[self] = "increment"
                   /\ sequencer' = [sequencer EXCEPT ![self] = @ + 1]
                   /\ pc' = [pc EXCEPT ![self] = "newMsg"]
                   /\ UNCHANGED << msgQs, stack, src, op, resp, objects, obj, 
                                   next_, objLogs_, op_, resp_, client, prev_, 
                                   objLogs_t, op_t, resp_t, requester_, prev, 
                                   next, objLogs, op_n, resp_n, requester >>

client_(self) == newMsg(self) \/ newObj(self) \/ increment(self)

listen_ == /\ pc["head"] = "listen_"
           /\ client' = (\E c \in PotentialRequestClients(head): msgQs[<<c, head>>] /= << >>)
           /\ pc' = [pc EXCEPT !["head"] = "incomingClientReq"]
           /\ UNCHANGED << msgQs, stack, src, op, resp, sequencer, objects, 
                           obj, next_, objLogs_, op_, resp_, prev_, objLogs_t, 
                           op_t, resp_t, requester_, prev, next, objLogs, op_n, 
                           resp_n, requester >>

incomingClientReq == /\ pc["head"] = "incomingClientReq"
                     /\ msgQs[(<<client, head>>)] /= << >>
                     /\ op_' = Head(msgQs[(<<client, head>>)])
                     /\ msgQs' = [msgQs EXCEPT ![(<<client, head>>)] = Tail(@)]
                     /\ IF op_'.action = READ
                           THEN /\ pc' = [pc EXCEPT !["head"] = "readingOjb_"]
                           ELSE /\ pc' = [pc EXCEPT !["head"] = "dirtyWrite_"]
                     /\ UNCHANGED << stack, src, op, resp, sequencer, objects, 
                                     obj, next_, objLogs_, resp_, client, 
                                     prev_, objLogs_t, op_t, resp_t, 
                                     requester_, prev, next, objLogs, op_n, 
                                     resp_n, requester >>

readingOjb_ == /\ pc["head"] = "readingOjb_"
               /\ IF isDirtyVersion(objLogs_, op_.obj)
                     THEN /\ /\ op' = [op EXCEPT !["head"] = op_]
                             /\ resp' = [resp EXCEPT !["head"] = resp_]
                             /\ src' = [src EXCEPT !["head"] = head]
                             /\ stack' = [stack EXCEPT !["head"] = << [ procedure |->  "apportionQuery",
                                                                        pc        |->  "respondToClient_",
                                                                        src       |->  src["head"],
                                                                        op        |->  op["head"],
                                                                        resp      |->  resp["head"] ] >>
                                                                    \o stack["head"]]
                          /\ pc' = [pc EXCEPT !["head"] = "sendQuery"]
                          /\ resp_' = resp_
                     ELSE /\ resp_' = readObjFromSelf(objLogs_, op_.obj)
                          /\ pc' = [pc EXCEPT !["head"] = "respondToClient_"]
                          /\ UNCHANGED << stack, src, op, resp >>
               /\ UNCHANGED << msgQs, sequencer, objects, obj, next_, objLogs_, 
                               op_, client, prev_, objLogs_t, op_t, resp_t, 
                               requester_, prev, next, objLogs, op_n, resp_n, 
                               requester >>

respondToClient_ == /\ pc["head"] = "respondToClient_"
                    /\ msgQs' = [msgQs EXCEPT ![(<<head, client>>)] = Append(@, resp_)]
                    /\ pc' = [pc EXCEPT !["head"] = "listen_"]
                    /\ UNCHANGED << stack, src, op, resp, sequencer, objects, 
                                    obj, next_, objLogs_, op_, resp_, client, 
                                    prev_, objLogs_t, op_t, resp_t, requester_, 
                                    prev, next, objLogs, op_n, resp_n, 
                                    requester >>

dirtyWrite_ == /\ pc["head"] = "dirtyWrite_"
               /\ objLogs_' = [objLogs_ EXCEPT ![(op_.obj)] = Append(@, [uniqueId |-> op_.uniqueId, isDirty |-> TRUE])]
               /\ pc' = [pc EXCEPT !["head"] = "propagate_"]
               /\ UNCHANGED << msgQs, stack, src, op, resp, sequencer, objects, 
                               obj, next_, op_, resp_, client, prev_, 
                               objLogs_t, op_t, resp_t, requester_, prev, next, 
                               objLogs, op_n, resp_n, requester >>

propagate_ == /\ pc["head"] = "propagate_"
              /\ msgQs' = [msgQs EXCEPT ![(<<head, next_>>)] = Append(@, op_)]
              /\ pc' = [pc EXCEPT !["head"] = "recvAck_"]
              /\ UNCHANGED << stack, src, op, resp, sequencer, objects, obj, 
                              next_, objLogs_, op_, resp_, client, prev_, 
                              objLogs_t, op_t, resp_t, requester_, prev, next, 
                              objLogs, op_n, resp_n, requester >>

recvAck_ == /\ pc["head"] = "recvAck_"
            /\ msgQs[(<<next_, head>>)] /= << >>
            /\ resp_' = Head(msgQs[(<<next_, head>>)])
            /\ msgQs' = [msgQs EXCEPT ![(<<next_, head>>)] = Tail(@)]
            /\ pc' = [pc EXCEPT !["head"] = "applyWrite_"]
            /\ UNCHANGED << stack, src, op, resp, sequencer, objects, obj, 
                            next_, objLogs_, op_, client, prev_, objLogs_t, 
                            op_t, resp_t, requester_, prev, next, objLogs, 
                            op_n, resp_n, requester >>

applyWrite_ == /\ pc["head"] = "applyWrite_"
               /\ objLogs_' = [objLogs_ EXCEPT ![op_.obj].isDirty = FALSE]
               /\ pc' = [pc EXCEPT !["head"] = "ackSuccessfulWrite_"]
               /\ UNCHANGED << msgQs, stack, src, op, resp, sequencer, objects, 
                               obj, next_, op_, resp_, client, prev_, 
                               objLogs_t, op_t, resp_t, requester_, prev, next, 
                               objLogs, op_n, resp_n, requester >>

ackSuccessfulWrite_ == /\ pc["head"] = "ackSuccessfulWrite_"
                       /\ resp_' = [  obj |-> op_.obj,
                                       uniqueId |-> op_.uniqueId,
                                       action |-> TRUE]
                       /\ msgQs' = [msgQs EXCEPT ![(<<head, client>>)] = Append(@, resp_')]
                       /\ pc' = [pc EXCEPT !["head"] = "listen_"]
                       /\ UNCHANGED << stack, src, op, resp, sequencer, 
                                       objects, obj, next_, objLogs_, op_, 
                                       client, prev_, objLogs_t, op_t, resp_t, 
                                       requester_, prev, next, objLogs, op_n, 
                                       resp_n, requester >>

headProcess == listen_ \/ incomingClientReq \/ readingOjb_
                  \/ respondToClient_ \/ dirtyWrite_ \/ propagate_
                  \/ recvAck_ \/ applyWrite_ \/ ackSuccessfulWrite_

listen_t == /\ pc["tail"] = "listen_t"
            /\ requester_' = (\E n \in PotentialRequestClients(tail) : msgQs[<<n, tail>>] /= << >>)
            /\ pc' = [pc EXCEPT !["tail"] = "incomingReq_"]
            /\ UNCHANGED << msgQs, stack, src, op, resp, sequencer, objects, 
                            obj, next_, objLogs_, op_, resp_, client, prev_, 
                            objLogs_t, op_t, resp_t, prev, next, objLogs, op_n, 
                            resp_n, requester >>

incomingReq_ == /\ pc["tail"] = "incomingReq_"
                /\ msgQs[(<<requester_, tail>>)] /= << >>
                /\ op_t' = Head(msgQs[(<<requester_, tail>>)])
                /\ msgQs' = [msgQs EXCEPT ![(<<requester_, tail>>)] = Tail(@)]
                /\ IF op_t'.action = READ
                      THEN /\ pc' = [pc EXCEPT !["tail"] = "readObj"]
                      ELSE /\ pc' = [pc EXCEPT !["tail"] = "applyWrite_t"]
                /\ UNCHANGED << stack, src, op, resp, sequencer, objects, obj, 
                                next_, objLogs_, op_, resp_, client, prev_, 
                                objLogs_t, resp_t, requester_, prev, next, 
                                objLogs, op_n, resp_n, requester >>

readObj == /\ pc["tail"] = "readObj"
           /\ resp_t' = readObjFromSelf(objLogs_t, op_t.obj)
           /\ pc' = [pc EXCEPT !["tail"] = "respond"]
           /\ UNCHANGED << msgQs, stack, src, op, resp, sequencer, objects, 
                           obj, next_, objLogs_, op_, resp_, client, prev_, 
                           objLogs_t, op_t, requester_, prev, next, objLogs, 
                           op_n, resp_n, requester >>

respond == /\ pc["tail"] = "respond"
           /\ msgQs' = [msgQs EXCEPT ![(<<tail, requester_>>)] = Append(@, resp_t)]
           /\ pc' = [pc EXCEPT !["tail"] = "listen_t"]
           /\ UNCHANGED << stack, src, op, resp, sequencer, objects, obj, 
                           next_, objLogs_, op_, resp_, client, prev_, 
                           objLogs_t, op_t, resp_t, requester_, prev, next, 
                           objLogs, op_n, resp_n, requester >>

applyWrite_t == /\ pc["tail"] = "applyWrite_t"
                /\ objLogs_t' = [objLogs_t EXCEPT ![op_t.obj] = Append(objLogs_t[op_t.obj], [uniqueId |-> op_t.uniqueId, isDirty |-> FALSE])]
                /\ pc' = [pc EXCEPT !["tail"] = "ackSuccessfulWrite_t"]
                /\ UNCHANGED << msgQs, stack, src, op, resp, sequencer, 
                                objects, obj, next_, objLogs_, op_, resp_, 
                                client, prev_, op_t, resp_t, requester_, prev, 
                                next, objLogs, op_n, resp_n, requester >>

ackSuccessfulWrite_t == /\ pc["tail"] = "ackSuccessfulWrite_t"
                        /\ resp_t' = [  obj |-> op_t.obj,
                                         uniqueId |-> op_t.uniqueId,
                                         action |-> TRUE]
                        /\ msgQs' = [msgQs EXCEPT ![(<<tail, requester_>>)] = Append(@, resp_t')]
                        /\ pc' = [pc EXCEPT !["tail"] = "listen_t"]
                        /\ UNCHANGED << stack, src, op, resp, sequencer, 
                                        objects, obj, next_, objLogs_, op_, 
                                        resp_, client, prev_, objLogs_t, op_t, 
                                        requester_, prev, next, objLogs, op_n, 
                                        resp_n, requester >>

tailProcess == listen_t \/ incomingReq_ \/ readObj \/ respond
                  \/ applyWrite_t \/ ackSuccessfulWrite_t

listen(self) == /\ pc[self] = "listen"
                /\ requester' = [requester EXCEPT ![self] = \E n \in PotentialRequestClients(self) : msgQs[<<n, self>>] /= << >>]
                /\ pc' = [pc EXCEPT ![self] = "incomingReq"]
                /\ UNCHANGED << msgQs, stack, src, op, resp, sequencer, 
                                objects, obj, next_, objLogs_, op_, resp_, 
                                client, prev_, objLogs_t, op_t, resp_t, 
                                requester_, prev, next, objLogs, op_n, resp_n >>

incomingReq(self) == /\ pc[self] = "incomingReq"
                     /\ msgQs[(<<requester[self], self>>)] /= << >>
                     /\ op_n' = [op_n EXCEPT ![self] = Head(msgQs[(<<requester[self], self>>)])]
                     /\ msgQs' = [msgQs EXCEPT ![(<<requester[self], self>>)] = Tail(@)]
                     /\ IF op_n'[self].action = READ
                           THEN /\ pc' = [pc EXCEPT ![self] = "readingOjb"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "dirtyWrite"]
                     /\ UNCHANGED << stack, src, op, resp, sequencer, objects, 
                                     obj, next_, objLogs_, op_, resp_, client, 
                                     prev_, objLogs_t, op_t, resp_t, 
                                     requester_, prev, next, objLogs, resp_n, 
                                     requester >>

readingOjb(self) == /\ pc[self] = "readingOjb"
                    /\ IF isDirtyVersion(objLogs[self], op_n[self].obj)
                          THEN /\ /\ op' = [op EXCEPT ![self] = op_n[self]]
                                  /\ resp' = [resp EXCEPT ![self] = resp_n[self]]
                                  /\ src' = [src EXCEPT ![self] = self]
                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "apportionQuery",
                                                                           pc        |->  "respondToClient",
                                                                           src       |->  src[self],
                                                                           op        |->  op[self],
                                                                           resp      |->  resp[self] ] >>
                                                                       \o stack[self]]
                               /\ pc' = [pc EXCEPT ![self] = "sendQuery"]
                               /\ UNCHANGED resp_n
                          ELSE /\ resp_n' = [resp_n EXCEPT ![self] = readObjFromSelf(objLogs[self], op_n[self].obj)]
                               /\ pc' = [pc EXCEPT ![self] = "respondToClient"]
                               /\ UNCHANGED << stack, src, op, resp >>
                    /\ UNCHANGED << msgQs, sequencer, objects, obj, next_, 
                                    objLogs_, op_, resp_, client, prev_, 
                                    objLogs_t, op_t, resp_t, requester_, prev, 
                                    next, objLogs, op_n, requester >>

respondToClient(self) == /\ pc[self] = "respondToClient"
                         /\ msgQs' = [msgQs EXCEPT ![(<<self, requester[self]>>)] = Append(@, resp_n[self])]
                         /\ pc' = [pc EXCEPT ![self] = "listen"]
                         /\ UNCHANGED << stack, src, op, resp, sequencer, 
                                         objects, obj, next_, objLogs_, op_, 
                                         resp_, client, prev_, objLogs_t, op_t, 
                                         resp_t, requester_, prev, next, 
                                         objLogs, op_n, resp_n, requester >>

dirtyWrite(self) == /\ pc[self] = "dirtyWrite"
                    /\ objLogs' = [objLogs EXCEPT ![self][(op_n[self].obj)] = Append(@, [uniqueId |-> op_n[self].uniqueId, isDirty |-> TRUE])]
                    /\ pc' = [pc EXCEPT ![self] = "propagate"]
                    /\ UNCHANGED << msgQs, stack, src, op, resp, sequencer, 
                                    objects, obj, next_, objLogs_, op_, resp_, 
                                    client, prev_, objLogs_t, op_t, resp_t, 
                                    requester_, prev, next, op_n, resp_n, 
                                    requester >>

propagate(self) == /\ pc[self] = "propagate"
                   /\ msgQs' = [msgQs EXCEPT ![(<<self, next[self]>>)] = Append(@, op_n[self])]
                   /\ pc' = [pc EXCEPT ![self] = "recvAck"]
                   /\ UNCHANGED << stack, src, op, resp, sequencer, objects, 
                                   obj, next_, objLogs_, op_, resp_, client, 
                                   prev_, objLogs_t, op_t, resp_t, requester_, 
                                   prev, next, objLogs, op_n, resp_n, 
                                   requester >>

recvAck(self) == /\ pc[self] = "recvAck"
                 /\ msgQs[(<<prev[self], head>>)] /= << >>
                 /\ resp_n' = [resp_n EXCEPT ![self] = Head(msgQs[(<<prev[self], head>>)])]
                 /\ msgQs' = [msgQs EXCEPT ![(<<prev[self], head>>)] = Tail(@)]
                 /\ pc' = [pc EXCEPT ![self] = "applyWrite"]
                 /\ UNCHANGED << stack, src, op, resp, sequencer, objects, obj, 
                                 next_, objLogs_, op_, resp_, client, prev_, 
                                 objLogs_t, op_t, resp_t, requester_, prev, 
                                 next, objLogs, op_n, requester >>

applyWrite(self) == /\ pc[self] = "applyWrite"
                    /\ objLogs' = [objLogs EXCEPT ![self][op_n[self].obj].isDirty = FALSE]
                    /\ pc' = [pc EXCEPT ![self] = "ackSuccessfulWrite"]
                    /\ UNCHANGED << msgQs, stack, src, op, resp, sequencer, 
                                    objects, obj, next_, objLogs_, op_, resp_, 
                                    client, prev_, objLogs_t, op_t, resp_t, 
                                    requester_, prev, next, op_n, resp_n, 
                                    requester >>

ackSuccessfulWrite(self) == /\ pc[self] = "ackSuccessfulWrite"
                            /\ resp_n' = [resp_n EXCEPT ![self] = [   obj |-> op_n[self].obj,
                                                                      uniqueId |-> op_n[self].uniqueId,
                                                                      action |-> TRUE]]
                            /\ msgQs' = [msgQs EXCEPT ![(<<self, prev[self]>>)] = Append(@, resp_n'[self])]
                            /\ pc' = [pc EXCEPT ![self] = "listen"]
                            /\ UNCHANGED << stack, src, op, resp, sequencer, 
                                            objects, obj, next_, objLogs_, op_, 
                                            resp_, client, prev_, objLogs_t, 
                                            op_t, resp_t, requester_, prev, 
                                            next, objLogs, op_n, requester >>

n(self) == listen(self) \/ incomingReq(self) \/ readingOjb(self)
              \/ respondToClient(self) \/ dirtyWrite(self)
              \/ propagate(self) \/ recvAck(self) \/ applyWrite(self)
              \/ ackSuccessfulWrite(self)

Next == headProcess \/ tailProcess
           \/ (\E self \in ProcSet: apportionQuery(self))
           \/ (\E self \in Clients: client_(self))
           \/ (\E self \in Nodes \ {head, tail}: n(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in Clients : WF_vars(client_(self))
        /\ WF_vars(headProcess) /\ WF_vars(apportionQuery("head"))
        /\ WF_vars(tailProcess)
        /\ \A self \in Nodes \ {head, tail} : WF_vars(n(self)) /\ WF_vars(apportionQuery(self))

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Mon May 29 00:08:49 EDT 2023 by 72jen
\* Last modified Sat May 27 01:14:05 EDT 2023 by jenniferlam
\* Created Thu May 25 11:58:00 EDT 2023 by jenniferlam
