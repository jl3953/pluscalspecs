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

ASSUME  /\ head \in Nodes
        /\ tail \in Nodes
        /\ Cardinality(Nodes) >= 2
        /\ Cardinality(Edges) = Cardinality(Nodes \ {head}) * 2 + Cardinality(Nodes \ {tail}) * 2
        /\ Cardinality(Descendants) = Cardinality(Nodes \ {head})
        /\ Cardinality(Ancestors) = Cardinality(Nodes \ {tail})
-----------------------------------------------------------------------------

READ == TRUE
WRITE == ~READ
Actions == {READ, WRITE}

NULLOP == [ obj |-> CHOOSE o \in Objects: TRUE,
            uniqueId |-> CHOOSE i \in Int : TRUE,
            action |-> CHOOSE a \in Actions : TRUE]
            
\*NULLLOGENTRY == [   uniqueId |-> CHOOSE i \in Int : TRUE,
\*                    isDirty |-> CHOOSE b \in {TRUE, FALSE} : TRUE]
\* LogEntry == [uniqueId (int), isDirty (bool) ]
\* Operation == [obj (Object), uniqueId (int), action (Action)]

(****************************************************************************

--fair algorithm CRAQ {
        variables   msgQs = [e \in Edges |-> << >>],
                    clientMsgQs = [ ce \in ClientEdges |-> << >>];
\*                    
\*    fair process(c \in Clients) 
\*        variables x = 1;
\*    {
\*        temp: while (TRUE) {
\*            x := 1;
\*        }
\*    }

    fair process (name="head") 
        variables   next = Descendants[head],
                    op = NULLOP, 
                    reply = NULLOP,
                    client = CHOOSE c \in Clients: TRUE,
                    objLogs = [o \in Objects |-> << >>]; 
    {
        listen: while (TRUE) {
        
            client := CHOOSE c \in Clients : clientMsgQs[<<c, head>>] /= << >>;                                           
            
            incomingClientReq: op := Head(clientMsgQs[<<client, head>>]); 
            clientMsgQs[<<client, head>>] := Tail(clientMsgQs[<<client, head>>]);
            
            if (op.action = READ) {
                                
                if (Head(objLogs[op.obj]).isDirty) {
                
                        apportionQuery: msgQs[<<head, tail>>] := Append(msgQs[<<head, tail>>], op);
                        await msgQs[<<tail, head>>] /= << >>;
                        
                        returnFromTail: reply := Head(msgQs[<<tail, head>>]);
                        msgQs[<<tail, head>>] := Tail(msgQs[<<tail, head>>]);
                        clientMsgQs[<<head, client>>] := Append(clientMsgQs[<<head, client>>], reply); 
                    
                    
                    } else {
                    
                        readObj: reply := [ obj |-> op.obj, 
                                            uniqueId |-> Head(objLogs[op.obj]).uniqueId,
                                            action |-> WRITE];  
                        returnFromSelf: clientMsgQs[<<head, client>>] := Append(clientMsgQs[<<head, client>>], reply);
                    }
                } else {
                    
                    dirtyWrite: objLogs[op.obj] := Append(objLogs[op.obj], [uniqueId |-> op.uniqueId, isDirty |-> TRUE]);
                    
                    propagate: msgQs[<<head, next>>] := Append(msgQs[<<head, next>>], op);
                    
                    recvAck: await msgQs[<<next, head>>] /= << >>;
                    msgQs[<<next, head>>] := Tail(msgQs[<<next, head>>]);
                    
                    applyWrite: objLogs[op.obj].isDirty := FALSE;
                                 
                    ackSuccessfulWrite: reply := [  obj |-> op.obj,
                                                uniqueId |-> op.uniqueId,
                                                action |-> TRUE];
                    clientMsgQs[<<head, client>>] := Append(clientMsgQs[<<head, client>>], reply);                                         
                }
            
            }
        }
    }
    
    fair process (name="tail") 
        variables   prev = Ancestors[tail],
                    src = CHOOSE n \in Nodes : TRUE,
                    op = NULLOP,
                    reply = NULLOP,
                    objLogs = [o \in Obj |-> << >>];
    {
        listen: while (TRUE) {
            src := CHOOSE n \in Nodes : msgQs[<<n, tail>>] /= << >>;
            

            op := Head(msgQs[<<src, tail>>])
            msgQs[<<src, tail>>] := Tail(msgQs[<<src, tail>>])
            
            if (op.action = READ) {
                readObj: reply := [ obj |-> op.obj, 
                                    uniqueId |-> Head(objLogs[op.obj]).uniqueId,
                                    action |-> WRITE];  
                apportionResp: msgQs[<<tail, src>>] := Append(msgQs[<<tail, src>>], reply);
            } else {
            
                applyWrite: objLogs[op.obj] := Append(objLogs[op.obj], [uniqueId |-> op.uniqueId, isDirty |-> FALSE]);
                                 
                ackSuccessfulWrite: reply := [  obj |-> op.obj,
                                                uniqueId |-> op.uniqueId,
                                                action |-> TRUE];
                clientMsgQs[<<tail, src>>] := Append(clientMsgQs[<<tail, src>>], reply);     
            } 
        
        }
    }
\*    
\*    fair process nodeProcess(n \in Nodes \ {head, tail}) {
\*        listen: while (TRUE) {
\*        
\*        }
\*        
\*    }
}
****************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "7d739e68" /\ chksum(tla) = "81b843e7")
VARIABLES msgQs, clientMsgQs, pc, next, op, reply, client, objLogs

vars == << msgQs, clientMsgQs, pc, next, op, reply, client, objLogs >>

ProcSet == {"head"}

Init == (* Global variables *)
        /\ msgQs = [e \in Edges |-> << >>]
        /\ clientMsgQs = [ ce \in ClientEdges |-> << >>]
        (* Process name *)
        /\ next = Descendants[head]
        /\ op = NULLOP
        /\ reply = NULLOP
        /\ client = CHOOSE c \in Clients: TRUE
        /\ objLogs = [o \in Objects |-> << >>]
        /\ pc = [self \in ProcSet |-> "listen"]

listen == /\ pc["head"] = "listen"
          /\ client' = (CHOOSE c \in Clients : clientMsgQs[<<c, head>>] /= << >>)
          /\ pc' = [pc EXCEPT !["head"] = "incomingClientReq"]
          /\ UNCHANGED << msgQs, clientMsgQs, next, op, reply, objLogs >>

incomingClientReq == /\ pc["head"] = "incomingClientReq"
                     /\ op' = Head(clientMsgQs[<<client, head>>])
                     /\ clientMsgQs' = [clientMsgQs EXCEPT ![<<client, head>>] = Tail(clientMsgQs[<<client, head>>])]
                     /\ IF op'.action = READ
                           THEN /\ IF Head(objLogs[op'.obj]).isDirty
                                      THEN /\ pc' = [pc EXCEPT !["head"] = "apportionQuery"]
                                      ELSE /\ pc' = [pc EXCEPT !["head"] = "readObj"]
                           ELSE /\ pc' = [pc EXCEPT !["head"] = "dirtyWrite"]
                     /\ UNCHANGED << msgQs, next, reply, client, objLogs >>

dirtyWrite == /\ pc["head"] = "dirtyWrite"
              /\ objLogs' = [objLogs EXCEPT ![op.obj] = Append(objLogs[op.obj], [uniqueId |-> op.uniqueId, isDirty |-> TRUE])]
              /\ pc' = [pc EXCEPT !["head"] = "propagate"]
              /\ UNCHANGED << msgQs, clientMsgQs, next, op, reply, client >>

propagate == /\ pc["head"] = "propagate"
             /\ msgQs' = [msgQs EXCEPT ![<<head, next>>] = Append(msgQs[<<head, next>>], op)]
             /\ pc' = [pc EXCEPT !["head"] = "recvAck"]
             /\ UNCHANGED << clientMsgQs, next, op, reply, client, objLogs >>

recvAck == /\ pc["head"] = "recvAck"
           /\ msgQs[<<next, head>>] /= << >>
           /\ msgQs' = [msgQs EXCEPT ![<<next, head>>] = Tail(msgQs[<<next, head>>])]
           /\ pc' = [pc EXCEPT !["head"] = "applyWrite"]
           /\ UNCHANGED << clientMsgQs, next, op, reply, client, objLogs >>

applyWrite == /\ pc["head"] = "applyWrite"
              /\ objLogs' = [objLogs EXCEPT ![op.obj].isDirty = FALSE]
              /\ pc' = [pc EXCEPT !["head"] = "ackSuccessfulWrite"]
              /\ UNCHANGED << msgQs, clientMsgQs, next, op, reply, client >>

ackSuccessfulWrite == /\ pc["head"] = "ackSuccessfulWrite"
                      /\ reply' =  [  obj |-> op.obj,
                                  uniqueId |-> op.uniqueId,
                                  action |-> TRUE]
                      /\ clientMsgQs' = [clientMsgQs EXCEPT ![<<head, client>>] = Append(clientMsgQs[<<head, client>>], reply')]
                      /\ pc' = [pc EXCEPT !["head"] = "listen"]
                      /\ UNCHANGED << msgQs, next, op, client, objLogs >>

apportionQuery == /\ pc["head"] = "apportionQuery"
                  /\ msgQs' = [msgQs EXCEPT ![<<head, tail>>] = Append(msgQs[<<head, tail>>], op)]
                  /\ msgQs'[<<tail, head>>] /= << >>
                  /\ pc' = [pc EXCEPT !["head"] = "returnFromTail"]
                  /\ UNCHANGED << clientMsgQs, next, op, reply, client, 
                                  objLogs >>

returnFromTail == /\ pc["head"] = "returnFromTail"
                  /\ reply' = Head(msgQs[<<tail, head>>])
                  /\ msgQs' = [msgQs EXCEPT ![<<tail, head>>] = Tail(msgQs[<<tail, head>>])]
                  /\ clientMsgQs' = [clientMsgQs EXCEPT ![<<head, client>>] = Append(clientMsgQs[<<head, client>>], reply')]
                  /\ pc' = [pc EXCEPT !["head"] = "listen"]
                  /\ UNCHANGED << next, op, client, objLogs >>

readObj == /\ pc["head"] = "readObj"
           /\ reply' = [ obj |-> op.obj,
                         uniqueId |-> Head(objLogs[op.obj]).uniqueId,
                         action |-> WRITE]
           /\ pc' = [pc EXCEPT !["head"] = "returnFromSelf"]
           /\ UNCHANGED << msgQs, clientMsgQs, next, op, client, objLogs >>

returnFromSelf == /\ pc["head"] = "returnFromSelf"
                  /\ clientMsgQs' = [clientMsgQs EXCEPT ![<<head, client>>] = Append(clientMsgQs[<<head, client>>], reply)]
                  /\ pc' = [pc EXCEPT !["head"] = "listen"]
                  /\ UNCHANGED << msgQs, next, op, reply, client, objLogs >>

name == listen \/ incomingClientReq \/ dirtyWrite \/ propagate \/ recvAck
           \/ applyWrite \/ ackSuccessfulWrite \/ apportionQuery
           \/ returnFromTail \/ readObj \/ returnFromSelf

Next == name

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ WF_vars(name)

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sat May 27 01:14:05 EDT 2023 by jenniferlam
\* Last modified Fri May 26 12:21:24 EDT 2023 by 72jen
\* Created Thu May 25 11:58:00 EDT 2023 by jenniferlam
