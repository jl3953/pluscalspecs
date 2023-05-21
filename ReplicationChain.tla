-------------------------- MODULE ReplicationChain --------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Nodes, head, tail, NumMsgs

Backups == Nodes \ {head}

RECURSIVE FormChainTopology(_,_)
FormChainTopology(curr, nodes) ==   IF nodes = {} THEN {} 
                                    ELSE LET n == CHOOSE node \in nodes : TRUE
                                         IN  {<<curr, n>>} \cup FormChainTopology(n, nodes \ {n})
                                            
NextEdges == FormChainTopology(head, Nodes \ {head})
PrevEdges == { <<e[2], e[1]>> : e \in NextEdges } 
Edges == NextEdges \cup PrevEdges

Descendants == [n \in Nodes \ {tail} |-> LET e == CHOOSE edge \in NextEdges : edge[1] = n IN e[2]]
Ancestors == [n \in Nodes \ {head} |-> LET e == CHOOSE edge \in PrevEdges : edge[1] = n IN e[2]]

ASSUME  /\ head \in Nodes
        /\ tail \in Nodes
        /\ Cardinality(Nodes) >= 2
        /\ Cardinality(Edges) = Cardinality(Backups) * 2
        /\ Cardinality(Descendants) = Cardinality(Backups)
        /\ Cardinality(Ancestors) = Cardinality(Nodes \ {tail})
        
-----------------------------------------------------------------------------

(****************************************************************************
--fair algorithm Ricochet {
    variables   msgQs = [e \in Edges |-> << >>],
                logs = [n \in Nodes |-> << >>];
    
    fair process(processName="head") 
        variables   next = Descendants[head],
                    msg = 1;
    {
        incomingClientReq: while (msg =< NumMsgs) {
            propagate: msgQs[<<head, next>>] := Append(msgQs[<<head, next>>], msg);
            
            recvAck: await msgQs[<<next, head>>] /= << >>;
            msgQs[<<next, head>>] := Tail(msgQs[<<next, head>>]);
            
            apply: logs[head] := Append(logs[head], msg);
            
            newClientReq: msg := msg + 1
        }
    }
    
    
    fair process(b \in Backups) 
        variables   prev = Ancestors[self],
                    msg = 0;
    {
        listen: while (TRUE) {
            await msgQs[<<prev, self>>] /= << >>;
            
            recvMsg: msg := Head(msgQs[<<prev, self>>]);
            msgQs[<<prev, self>>] := Tail(msgQs[<<prev, self>>]);
            
            if (self /= tail) {
                forward: msgQs[<<self, Descendants[self]>>] := Append(msgQs[<<self, Descendants[self]>>], msg);
                    
                recvAck: await msgQs[<<Descendants[self], self>>] /= << >>;
                msgQs[<<Descendants[self], self>>] := Tail(msgQs[<<Descendants[self], self>>]);
            };
            
            apply: logs[self] := Append(logs[self], msg);
            
            ack: msgQs[<<self, prev>>] := Append(msgQs[<<self, prev>>], TRUE);
        }
    }
}
****************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "d4c12e66" /\ chksum(tla) = "d18bc952")
\* Label recvAck of process processName at line 42 col 22 changed to recvAck_
\* Label apply of process processName at line 45 col 20 changed to apply_
\* Process variable msg of process processName at line 37 col 21 changed to msg_
VARIABLES msgQs, logs, pc, next, msg_, prev, msg

vars == << msgQs, logs, pc, next, msg_, prev, msg >>

ProcSet == {"head"} \cup (Backups)

Init == (* Global variables *)
        /\ msgQs = [e \in Edges |-> << >>]
        /\ logs = [n \in Nodes |-> << >>]
        (* Process processName *)
        /\ next = Descendants[head]
        /\ msg_ = 1
        (* Process b *)
        /\ prev = [self \in Backups |-> Ancestors[self]]
        /\ msg = [self \in Backups |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self = "head" -> "incomingClientReq"
                                        [] self \in Backups -> "listen"]

incomingClientReq == /\ pc["head"] = "incomingClientReq"
                     /\ IF msg_ =< NumMsgs
                           THEN /\ pc' = [pc EXCEPT !["head"] = "propagate"]
                           ELSE /\ pc' = [pc EXCEPT !["head"] = "Done"]
                     /\ UNCHANGED << msgQs, logs, next, msg_, prev, msg >>

propagate == /\ pc["head"] = "propagate"
             /\ msgQs' = [msgQs EXCEPT ![<<head, next>>] = Append(msgQs[<<head, next>>], msg_)]
             /\ pc' = [pc EXCEPT !["head"] = "recvAck_"]
             /\ UNCHANGED << logs, next, msg_, prev, msg >>

recvAck_ == /\ pc["head"] = "recvAck_"
            /\ msgQs[<<next, head>>] /= << >>
            /\ msgQs' = [msgQs EXCEPT ![<<next, head>>] = Tail(msgQs[<<next, head>>])]
            /\ pc' = [pc EXCEPT !["head"] = "apply_"]
            /\ UNCHANGED << logs, next, msg_, prev, msg >>

apply_ == /\ pc["head"] = "apply_"
          /\ logs' = [logs EXCEPT ![head] = Append(logs[head], msg_)]
          /\ pc' = [pc EXCEPT !["head"] = "newClientReq"]
          /\ UNCHANGED << msgQs, next, msg_, prev, msg >>

newClientReq == /\ pc["head"] = "newClientReq"
                /\ msg_' = msg_ + 1
                /\ pc' = [pc EXCEPT !["head"] = "incomingClientReq"]
                /\ UNCHANGED << msgQs, logs, next, prev, msg >>

processName == incomingClientReq \/ propagate \/ recvAck_ \/ apply_
                  \/ newClientReq

listen(self) == /\ pc[self] = "listen"
                /\ msgQs[<<prev[self], self>>] /= << >>
                /\ pc' = [pc EXCEPT ![self] = "recvMsg"]
                /\ UNCHANGED << msgQs, logs, next, msg_, prev, msg >>

recvMsg(self) == /\ pc[self] = "recvMsg"
                 /\ msg' = [msg EXCEPT ![self] = Head(msgQs[<<prev[self], self>>])]
                 /\ msgQs' = [msgQs EXCEPT ![<<prev[self], self>>] = Tail(msgQs[<<prev[self], self>>])]
                 /\ IF self /= tail
                       THEN /\ pc' = [pc EXCEPT ![self] = "forward"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "apply"]
                 /\ UNCHANGED << logs, next, msg_, prev >>

forward(self) == /\ pc[self] = "forward"
                 /\ msgQs' = [msgQs EXCEPT ![<<self, Descendants[self]>>] = Append(msgQs[<<self, Descendants[self]>>], msg[self])]
                 /\ pc' = [pc EXCEPT ![self] = "recvAck"]
                 /\ UNCHANGED << logs, next, msg_, prev, msg >>

recvAck(self) == /\ pc[self] = "recvAck"
                 /\ msgQs[<<Descendants[self], self>>] /= << >>
                 /\ msgQs' = [msgQs EXCEPT ![<<Descendants[self], self>>] = Tail(msgQs[<<Descendants[self], self>>])]
                 /\ pc' = [pc EXCEPT ![self] = "apply"]
                 /\ UNCHANGED << logs, next, msg_, prev, msg >>

apply(self) == /\ pc[self] = "apply"
               /\ logs' = [logs EXCEPT ![self] = Append(logs[self], msg[self])]
               /\ pc' = [pc EXCEPT ![self] = "ack"]
               /\ UNCHANGED << msgQs, next, msg_, prev, msg >>

ack(self) == /\ pc[self] = "ack"
             /\ msgQs' = [msgQs EXCEPT ![<<self, prev[self]>>] = Append(msgQs[<<self, prev[self]>>], TRUE)]
             /\ pc' = [pc EXCEPT ![self] = "listen"]
             /\ UNCHANGED << logs, next, msg_, prev, msg >>

b(self) == listen(self) \/ recvMsg(self) \/ forward(self) \/ recvAck(self)
              \/ apply(self) \/ ack(self)

Next == processName
           \/ (\E self \in Backups: b(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ WF_vars(processName)
        /\ \A self \in Backups : WF_vars(b(self))

\* END TRANSLATION 

Terminated == Len(logs[head]) = NumMsgs

PostCondition == \A backup \in Backups: logs[backup] = logs[head]

PrefixInvariant == \A backup \in Backups: SubSeq(logs[backup], 1, Len(logs[head])) = logs[head]
=============================================================================
\* Modification History
\* Last modified Fri May 19 22:57:39 EDT 2023 by 72jen
\* tail modified Fri May 19 19:05:47 EDT 2023 by 72jen
\* Created Fri May 19 17:43:43 EDT 2023 by 72jen
