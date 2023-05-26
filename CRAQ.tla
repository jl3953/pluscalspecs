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
            
NULLLOGENTRY == [   uniqueId |-> CHOOSE i \in Int : TRUE,
                    isDirty |-> CHOOSE b \in {TRUE, FALSE} : TRUE]
\* LogEntry == [uniqueId (int), isDirty (bool) ]
\* Operation == [obj (Object), uniqueId (int), action (Action)]

(****************************************************************************

--fair algorithm CRAQ {
        variables   msgQs = [e \in Edges |-> << >>],
                    clientMsgQs = [ ce \in ClientEdges |-> << >>];
                    
    fair process(c \in Clients) 
        variables x = 1;
    {
        temp: while (TRUE) {
            x := 1;
        }
    }

    fair process (name="head") 
        variables   next = Descendants[head],
                    op = NULLOP, 
                    reply = NULLOP,
                    objLogs = [o \in Objects |-> << >>]; 
    {
        listen: while (TRUE) {
        
            with (client \in {c \in Clients : clientMsgQs[<<c, head>>] /= << >>}) {
                                                       
                op := Head(clientMsgQs[<<client, head>>]); 
                clientMsgQs[<<client, head>>] := Tail(clientMsgQs[<<client, head>>]);
            
                if (op.action = READ) {
   
                    if (Head(objLogs[op.obj]).isDirty) {
                
                        apportionQuery: msgQs[<<head, tail>>] := Append(msgQs[<<head, tail>>], op)
                        await msgQs[<<tail, head>>] /= << >>;
                        reply := Head(msgQs<<tail, head>>);
                        msgQs<<tail, head>> := Tail(msgQs<<tail, head>>);
                    
                        returnToClient: clientMsgQs[<<head, client>>] := Append(clientMsgQs[<<head, client>>], reply); 
                    
                    
                    } else {
                    
                        readObj: reply := [ obj |-> op.obj, 
                                            uniqueId |-> Head(objLogs[op.obj]).uniqueId,
                                            action |-> WRITE];  
                        returnToClient: clientMsgQs[<<head, client>>] := Append(clientMsgQs[<<head, client>>], reply);
                    }
                } else {
                    
                    dirtyWrite: objLogs[op.obj] := Append(objLogs[op.obj], [uniqueId |-> op.uniqueId, isDirty |-> TRUE]);
                    
                    propagate: msgQs[<<head, next>>] := Append(msgQs[<<head, next>>], op);
                    
                    recvAck: await msgQs<<next, head>> /= << >>;
                    msgQs<<next, head>> := Tail(msgQs<<next, head>>);
                    
                    applyWrite: objLogs[op.obj].isDirty := FALSE;
                                 
                    returnToClient: reply := [  obj |-> op.obj,
                                                uniqueId |-> op.uniqueId,
                                                action |-> TRUE];
                    clientMsgQs[<<head, client>>] := Append(clientMsgQs[<<head, client>>], reply);                                         
                }
            
            }
        }
    }
    
\*    fair process tailProcess(name="tail") {
\*        listen: while (TRUE) {
\*        
\*        }
\*    }
\*    
\*    fair process nodeProcess(n \in Nodes \ {head, tail}) {
\*        listen: while (TRUE) {
\*        
\*        }
\*        
\*    }
    
}
****************************************************************************)

=============================================================================
\* Modification History
\* Last modified Thu May 25 18:14:22 EDT 2023 by jenniferlam
\* Created Thu May 25 11:58:00 EDT 2023 by jenniferlam
