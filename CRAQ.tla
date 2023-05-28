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
                    

            
\*EdgesToSelf(n) == { e \in Network : e[2] = n }
\*EdgesFromSelf(n) == { e \in Network : e[1] = n}
\*ClientEdgesToSelf(n) == { e \in ClientEdges : e[2] = n}
\*ClientEdgesFromSelf(n) == { e \in ClientEdges : e[1] = n}

\* LogEntry == [uniqueId (int), isDirty (bool) ]
\* Operation == [obj (Object), uniqueId (int), action (Action)]

(****************************************************************************

--fair algorithm CRAQ {
        variables   msgQs = [e \in Network |-> << >>];
        
        define {
            
            PotentialRequestClients(n) == IF n = head THEN Clients ELSE {Ancestors[n]} \cup Clients

            readObjFromSelf(objLogs, obj) == [  obj |-> obj, 
                                                uniqueId |-> Head(objLogs[obj]).uniqueId, 
                                                action |-> WRITE]
            isDirtyVersion(objLogs, obj) == Head(objLogs[obj]).isDirty
        }
        
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
        
        procedure apportionQuery(src, op, resp) {
            sendQuery: send(<<src, tail>>, op);
            rcvResp: rcv(<<tail, src>>, resp); 
        }
                    
    fair process(client \in Clients) 
        variables x = 1;
    {
        temp: while (TRUE) {
            x := 1;
        }
    }

    fair process (h="head") 
        variables   next = Descendants[head],
                    op = NULLOP, 
                    resp = NULLOP,
                    client = CHOOSE c \in Clients: TRUE,
                    objLogs = [o \in Objects |-> << >>]; 
    {
        listen: 
        while (TRUE) {
        
            client := CHOOSE c \in PotentialRequestClients(head): msgQs[<<c, head>>] /= << >>;
                                                       
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
    
    fair process (t="tail") 
        variables   prev = Ancestors[tail],
                    src = CHOOSE n \in Nodes : TRUE,
                    op = NULLOP,
                    resp = NULLOP,
                    requester = CHOOSE n \in Nodes \cup Clients : TRUE,
                    objLogs = [o \in Objects |-> << >>];
    {
        listen: while (TRUE) {
            requester := CHOOSE n \in PotentialRequestClients(tail) : msgQs[<<n, tail>>] /= << >>;
            
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
    
\*    fair process replica(n \in Nodes \ {head, tail}) {
\*        listen: while (TRUE) {
\*        
\*        }
\*        
\*    }
}
****************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "dca86f9f" /\ chksum(tla) = "8649cec7")
\* Label listen of process h at line 110 col 9 changed to listen_
\* Label applyWrite of process h at line 134 col 29 changed to applyWrite_
\* Label ackSuccessfulWrite of process h at line 136 col 37 changed to ackSuccessfulWrite_
\* Process client at line 94 col 10 changed to client_
\* Process variable op of process h at line 104 col 21 changed to op_
\* Process variable resp of process h at line 105 col 21 changed to resp_
\* Process variable objLogs of process h at line 107 col 21 changed to objLogs_
\* Process variable src of process t at line 146 col 21 changed to src_
\* Process variable op of process t at line 147 col 21 changed to op_t
\* Process variable resp of process t at line 148 col 21 changed to resp_t
CONSTANT defaultInitValue
VARIABLES msgQs, pc, stack

(* define statement *)
PotentialRequestClients(n) == IF n = head THEN Clients ELSE {Ancestors[n]} \cup Clients

readObjFromSelf(objLogs, obj) == [  obj |-> obj,
                                    uniqueId |-> Head(objLogs[obj]).uniqueId,
                                    action |-> WRITE]
isDirtyVersion(objLogs, obj) == Head(objLogs[obj]).isDirty

VARIABLES src, op, resp, x, next, op_, resp_, client, objLogs_, prev, src_, 
          op_t, resp_t, requester, objLogs

vars == << msgQs, pc, stack, src, op, resp, x, next, op_, resp_, client, 
           objLogs_, prev, src_, op_t, resp_t, requester, objLogs >>

ProcSet == (Clients) \cup {"head"} \cup {"tail"}

Init == (* Global variables *)
        /\ msgQs = [e \in Network |-> << >>]
        (* Procedure apportionQuery *)
        /\ src = [ self \in ProcSet |-> defaultInitValue]
        /\ op = [ self \in ProcSet |-> defaultInitValue]
        /\ resp = [ self \in ProcSet |-> defaultInitValue]
        (* Process client_ *)
        /\ x = [self \in Clients |-> 1]
        (* Process h *)
        /\ next = Descendants[head]
        /\ op_ = NULLOP
        /\ resp_ = NULLOP
        /\ client = CHOOSE c \in Clients: TRUE
        /\ objLogs_ = [o \in Objects |-> << >>]
        (* Process t *)
        /\ prev = Ancestors[tail]
        /\ src_ = CHOOSE n \in Nodes : TRUE
        /\ op_t = NULLOP
        /\ resp_t = NULLOP
        /\ requester = CHOOSE n \in Nodes \cup Clients : TRUE
        /\ objLogs = [o \in Objects |-> << >>]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "temp"
                                        [] self = "head" -> "listen_"
                                        [] self = "tail" -> "listen"]

sendQuery(self) == /\ pc[self] = "sendQuery"
                   /\ msgQs' = [msgQs EXCEPT ![(<<src[self], tail>>)] = Append(@, op[self])]
                   /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                   /\ UNCHANGED << stack, src, op, resp, x, next, op_, resp_, 
                                   client, objLogs_, prev, src_, op_t, resp_t, 
                                   requester, objLogs >>

rcvResp(self) == /\ pc[self] = "rcvResp"
                 /\ msgQs[(<<tail, src[self]>>)] /= << >>
                 /\ resp' = [resp EXCEPT ![self] = Head(msgQs[(<<tail, src[self]>>)])]
                 /\ msgQs' = [msgQs EXCEPT ![(<<tail, src[self]>>)] = Tail(@)]
                 /\ pc' = [pc EXCEPT ![self] = "Error"]
                 /\ UNCHANGED << stack, src, op, x, next, op_, resp_, client, 
                                 objLogs_, prev, src_, op_t, resp_t, requester, 
                                 objLogs >>

apportionQuery(self) == sendQuery(self) \/ rcvResp(self)

temp(self) == /\ pc[self] = "temp"
              /\ x' = [x EXCEPT ![self] = 1]
              /\ pc' = [pc EXCEPT ![self] = "temp"]
              /\ UNCHANGED << msgQs, stack, src, op, resp, next, op_, resp_, 
                              client, objLogs_, prev, src_, op_t, resp_t, 
                              requester, objLogs >>

client_(self) == temp(self)

listen_ == /\ pc["head"] = "listen_"
           /\ client' = (CHOOSE c \in PotentialRequestClients(head): msgQs[<<c, head>>] /= << >>)
           /\ pc' = [pc EXCEPT !["head"] = "incomingClientReq"]
           /\ UNCHANGED << msgQs, stack, src, op, resp, x, next, op_, resp_, 
                           objLogs_, prev, src_, op_t, resp_t, requester, 
                           objLogs >>

incomingClientReq == /\ pc["head"] = "incomingClientReq"
                     /\ msgQs[(<<client, head>>)] /= << >>
                     /\ op_' = Head(msgQs[(<<client, head>>)])
                     /\ msgQs' = [msgQs EXCEPT ![(<<client, head>>)] = Tail(@)]
                     /\ IF op_'.action = READ
                           THEN /\ pc' = [pc EXCEPT !["head"] = "readingOjb"]
                           ELSE /\ pc' = [pc EXCEPT !["head"] = "dirtyWrite"]
                     /\ UNCHANGED << stack, src, op, resp, x, next, resp_, 
                                     client, objLogs_, prev, src_, op_t, 
                                     resp_t, requester, objLogs >>

readingOjb == /\ pc["head"] = "readingOjb"
              /\ IF isDirtyVersion(objLogs_, op_.obj)
                    THEN /\ /\ op' = [op EXCEPT !["head"] = op_]
                            /\ resp' = [resp EXCEPT !["head"] = resp_]
                            /\ src' = [src EXCEPT !["head"] = head]
                            /\ stack' = [stack EXCEPT !["head"] = << [ procedure |->  "apportionQuery",
                                                                       pc        |->  "respondToClient",
                                                                       src       |->  src["head"],
                                                                       op        |->  op["head"],
                                                                       resp      |->  resp["head"] ] >>
                                                                   \o stack["head"]]
                         /\ pc' = [pc EXCEPT !["head"] = "sendQuery"]
                         /\ resp_' = resp_
                    ELSE /\ resp_' = readObjFromSelf(objLogs_, op_.obj)
                         /\ pc' = [pc EXCEPT !["head"] = "respondToClient"]
                         /\ UNCHANGED << stack, src, op, resp >>
              /\ UNCHANGED << msgQs, x, next, op_, client, objLogs_, prev, 
                              src_, op_t, resp_t, requester, objLogs >>

respondToClient == /\ pc["head"] = "respondToClient"
                   /\ msgQs' = [msgQs EXCEPT ![(<<head, client>>)] = Append(@, resp_)]
                   /\ pc' = [pc EXCEPT !["head"] = "listen_"]
                   /\ UNCHANGED << stack, src, op, resp, x, next, op_, resp_, 
                                   client, objLogs_, prev, src_, op_t, resp_t, 
                                   requester, objLogs >>

dirtyWrite == /\ pc["head"] = "dirtyWrite"
              /\ objLogs_' = [objLogs_ EXCEPT ![(op_.obj)] = Append(@, [uniqueId |-> op_.uniqueId, isDirty |-> TRUE])]
              /\ pc' = [pc EXCEPT !["head"] = "propagate"]
              /\ UNCHANGED << msgQs, stack, src, op, resp, x, next, op_, resp_, 
                              client, prev, src_, op_t, resp_t, requester, 
                              objLogs >>

propagate == /\ pc["head"] = "propagate"
             /\ msgQs' = [msgQs EXCEPT ![(<<head, next>>)] = Append(@, op_)]
             /\ pc' = [pc EXCEPT !["head"] = "recvAck"]
             /\ UNCHANGED << stack, src, op, resp, x, next, op_, resp_, client, 
                             objLogs_, prev, src_, op_t, resp_t, requester, 
                             objLogs >>

recvAck == /\ pc["head"] = "recvAck"
           /\ msgQs[(<<next, head>>)] /= << >>
           /\ resp_' = Head(msgQs[(<<next, head>>)])
           /\ msgQs' = [msgQs EXCEPT ![(<<next, head>>)] = Tail(@)]
           /\ pc' = [pc EXCEPT !["head"] = "applyWrite_"]
           /\ UNCHANGED << stack, src, op, resp, x, next, op_, client, 
                           objLogs_, prev, src_, op_t, resp_t, requester, 
                           objLogs >>

applyWrite_ == /\ pc["head"] = "applyWrite_"
               /\ objLogs_' = [objLogs_ EXCEPT ![op_.obj].isDirty = FALSE]
               /\ pc' = [pc EXCEPT !["head"] = "ackSuccessfulWrite_"]
               /\ UNCHANGED << msgQs, stack, src, op, resp, x, next, op_, 
                               resp_, client, prev, src_, op_t, resp_t, 
                               requester, objLogs >>

ackSuccessfulWrite_ == /\ pc["head"] = "ackSuccessfulWrite_"
                       /\ resp_' = [  obj |-> op_.obj,
                                       uniqueId |-> op_.uniqueId,
                                       action |-> TRUE]
                       /\ msgQs' = [msgQs EXCEPT ![(<<head, client>>)] = Append(@, resp_')]
                       /\ pc' = [pc EXCEPT !["head"] = "listen_"]
                       /\ UNCHANGED << stack, src, op, resp, x, next, op_, 
                                       client, objLogs_, prev, src_, op_t, 
                                       resp_t, requester, objLogs >>

h == listen_ \/ incomingClientReq \/ readingOjb \/ respondToClient
        \/ dirtyWrite \/ propagate \/ recvAck \/ applyWrite_
        \/ ackSuccessfulWrite_

listen == /\ pc["tail"] = "listen"
          /\ requester' = (CHOOSE n \in PotentialRequestClients(tail) : msgQs[<<n, tail>>] /= << >>)
          /\ pc' = [pc EXCEPT !["tail"] = "incomingReq"]
          /\ UNCHANGED << msgQs, stack, src, op, resp, x, next, op_, resp_, 
                          client, objLogs_, prev, src_, op_t, resp_t, objLogs >>

incomingReq == /\ pc["tail"] = "incomingReq"
               /\ msgQs[(<<requester, tail>>)] /= << >>
               /\ op_t' = Head(msgQs[(<<requester, tail>>)])
               /\ msgQs' = [msgQs EXCEPT ![(<<requester, tail>>)] = Tail(@)]
               /\ IF op_t'.action = READ
                     THEN /\ pc' = [pc EXCEPT !["tail"] = "readObj"]
                     ELSE /\ pc' = [pc EXCEPT !["tail"] = "applyWrite"]
               /\ UNCHANGED << stack, src, op, resp, x, next, op_, resp_, 
                               client, objLogs_, prev, src_, resp_t, requester, 
                               objLogs >>

readObj == /\ pc["tail"] = "readObj"
           /\ resp_t' = readObjFromSelf(objLogs, op_t.obj)
           /\ pc' = [pc EXCEPT !["tail"] = "respond"]
           /\ UNCHANGED << msgQs, stack, src, op, resp, x, next, op_, resp_, 
                           client, objLogs_, prev, src_, op_t, requester, 
                           objLogs >>

respond == /\ pc["tail"] = "respond"
           /\ msgQs' = [msgQs EXCEPT ![(<<tail, requester>>)] = Append(@, resp_t)]
           /\ pc' = [pc EXCEPT !["tail"] = "listen"]
           /\ UNCHANGED << stack, src, op, resp, x, next, op_, resp_, client, 
                           objLogs_, prev, src_, op_t, resp_t, requester, 
                           objLogs >>

applyWrite == /\ pc["tail"] = "applyWrite"
              /\ objLogs' = [objLogs EXCEPT ![op_t.obj] = Append(objLogs[op_t.obj], [uniqueId |-> op_t.uniqueId, isDirty |-> FALSE])]
              /\ pc' = [pc EXCEPT !["tail"] = "ackSuccessfulWrite"]
              /\ UNCHANGED << msgQs, stack, src, op, resp, x, next, op_, resp_, 
                              client, objLogs_, prev, src_, op_t, resp_t, 
                              requester >>

ackSuccessfulWrite == /\ pc["tail"] = "ackSuccessfulWrite"
                      /\ resp_t' = [  obj |-> op_t.obj,
                                       uniqueId |-> op_t.uniqueId,
                                       action |-> TRUE]
                      /\ msgQs' = [msgQs EXCEPT ![(<<tail, requester>>)] = Append(@, resp_t')]
                      /\ pc' = [pc EXCEPT !["tail"] = "listen"]
                      /\ UNCHANGED << stack, src, op, resp, x, next, op_, 
                                      resp_, client, objLogs_, prev, src_, 
                                      op_t, requester, objLogs >>

t == listen \/ incomingReq \/ readObj \/ respond \/ applyWrite
        \/ ackSuccessfulWrite

Next == h \/ t
           \/ (\E self \in ProcSet: apportionQuery(self))
           \/ (\E self \in Clients: client_(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in Clients : WF_vars(client_(self))
        /\ WF_vars(h) /\ WF_vars(apportionQuery("head"))
        /\ WF_vars(t)

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sun May 28 17:00:44 EDT 2023 by 72jen
\* Last modified Sat May 27 01:14:05 EDT 2023 by jenniferlam
\* Created Thu May 25 11:58:00 EDT 2023 by jenniferlam
