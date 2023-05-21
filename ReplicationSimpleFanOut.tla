---------------------- MODULE ReplicationSimpleFanOut ----------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Nodes, primary, totalMsgs

\* Specifying fan-out topology
EdgesToPrimary == { <<n, primary>> : n \in Nodes \ {primary}}
EdgesFromPrimary == { <<primary, n>> : n \in Nodes \ {primary}}
Edges == EdgesToPrimary \cup EdgesFromPrimary

Backups == Nodes \ {primary}

ASSUME  /\ primary \in Nodes
        /\ Backups \cup {primary} = Nodes
        /\ Cardinality(Nodes) >= 2
        /\ Cardinality(Edges) = 2 * Cardinality(Backups)

----------------------------------------------------------------------------
        
(***************************************************************************
--fair algorithm FanOutMsgFromPrimary {
    variables   networkMsgs = [e \in Edges |-> << >>],
                logs = [n \in Nodes |-> << >>];
                
    fair process(processName = "primary")
        variables   acks = [n \in Backups |-> FALSE],
                    i = 1,
                    I = EdgesToPrimary;
        {
        clientReqs: while (i <= totalMsgs) {
            
            fanout: networkMsgs := [e \in Edges |-> IF e \in EdgesFromPrimary THEN
                                                        Append(networkMsgs[e], i)
                                                    ELSE
                                                        networkMsgs[e]
                                    ];
            waitForAcks: while (I /= {}) {
                recAck: with (e \in I) {
                    when networkMsgs[e] /= << >>;
                    acks[e[1]] := IF i = totalMsgs THEN Head(networkMsgs[e]) ELSE FALSE;
                    networkMsgs[e] := Tail(networkMsgs[e]);
                    I := I \ {e}; 
                };
            };
            
            apply: logs[primary] := Append(logs[primary], i);
            
            increment: I := EdgesToPrimary;
            i := i + 1;
        }     
    }
    
    fair process (node \in Backups) {
            listen: while (TRUE) {
                when networkMsgs[<<primary, self>>] /= << >>;
                apply: logs[self] := Append(logs[self], Head(networkMsgs[<<primary, self>>]));
                networkMsgs[<<primary, self>>] := Tail(networkMsgs[<<primary, self>>]);
                sendAck: networkMsgs[<<self, primary>>] := Append(networkMsgs[<<self, primary>>], TRUE);  
            }
    }
    
}

***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "24875a60" /\ chksum(tla) = "abc08e32")
\* Label apply of process processName at line 46 col 20 changed to apply_
VARIABLES networkMsgs, logs, pc, acks, i, I

vars == << networkMsgs, logs, pc, acks, i, I >>

ProcSet == {"primary"} \cup (Backups)

Init == (* Global variables *)
        /\ networkMsgs = [e \in Edges |-> << >>]
        /\ logs = [n \in Nodes |-> << >>]
        (* Process processName *)
        /\ acks = [n \in Backups |-> FALSE]
        /\ i = 1
        /\ I = EdgesToPrimary
        /\ pc = [self \in ProcSet |-> CASE self = "primary" -> "clientReqs"
                                        [] self \in Backups -> "listen"]

clientReqs == /\ pc["primary"] = "clientReqs"
              /\ IF i <= totalMsgs
                    THEN /\ pc' = [pc EXCEPT !["primary"] = "fanout"]
                    ELSE /\ pc' = [pc EXCEPT !["primary"] = "Done"]
              /\ UNCHANGED << networkMsgs, logs, acks, i, I >>

fanout == /\ pc["primary"] = "fanout"
          /\ networkMsgs' = [e \in Edges |-> IF e \in EdgesFromPrimary THEN
                                                 Append(networkMsgs[e], i)
                                             ELSE
                                                 networkMsgs[e]
                             ]
          /\ pc' = [pc EXCEPT !["primary"] = "waitForAcks"]
          /\ UNCHANGED << logs, acks, i, I >>

waitForAcks == /\ pc["primary"] = "waitForAcks"
               /\ IF I /= {}
                     THEN /\ pc' = [pc EXCEPT !["primary"] = "recAck"]
                     ELSE /\ pc' = [pc EXCEPT !["primary"] = "apply_"]
               /\ UNCHANGED << networkMsgs, logs, acks, i, I >>

recAck == /\ pc["primary"] = "recAck"
          /\ \E e \in I:
               /\ networkMsgs[e] /= << >>
               /\ acks' = [acks EXCEPT ![e[1]] = IF i = totalMsgs THEN Head(networkMsgs[e]) ELSE FALSE]
               /\ networkMsgs' = [networkMsgs EXCEPT ![e] = Tail(networkMsgs[e])]
               /\ I' = I \ {e}
          /\ pc' = [pc EXCEPT !["primary"] = "waitForAcks"]
          /\ UNCHANGED << logs, i >>

apply_ == /\ pc["primary"] = "apply_"
          /\ logs' = [logs EXCEPT ![primary] = Append(logs[primary], i)]
          /\ pc' = [pc EXCEPT !["primary"] = "increment"]
          /\ UNCHANGED << networkMsgs, acks, i, I >>

increment == /\ pc["primary"] = "increment"
             /\ I' = EdgesToPrimary
             /\ i' = i + 1
             /\ pc' = [pc EXCEPT !["primary"] = "clientReqs"]
             /\ UNCHANGED << networkMsgs, logs, acks >>

processName == clientReqs \/ fanout \/ waitForAcks \/ recAck \/ apply_
                  \/ increment

listen(self) == /\ pc[self] = "listen"
                /\ networkMsgs[<<primary, self>>] /= << >>
                /\ pc' = [pc EXCEPT ![self] = "apply"]
                /\ UNCHANGED << networkMsgs, logs, acks, i, I >>

apply(self) == /\ pc[self] = "apply"
               /\ logs' = [logs EXCEPT ![self] = Append(logs[self], Head(networkMsgs[<<primary, self>>]))]
               /\ networkMsgs' = [networkMsgs EXCEPT ![<<primary, self>>] = Tail(networkMsgs[<<primary, self>>])]
               /\ pc' = [pc EXCEPT ![self] = "sendAck"]
               /\ UNCHANGED << acks, i, I >>

sendAck(self) == /\ pc[self] = "sendAck"
                 /\ networkMsgs' = [networkMsgs EXCEPT ![<<self, primary>>] = Append(networkMsgs[<<self, primary>>], TRUE)]
                 /\ pc' = [pc EXCEPT ![self] = "listen"]
                 /\ UNCHANGED << logs, acks, i, I >>

node(self) == listen(self) \/ apply(self) \/ sendAck(self)

Next == processName
           \/ (\E self \in Backups: node(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ WF_vars(processName)
        /\ \A self \in Backups : WF_vars(node(self))

\* END TRANSLATION 
-----------------------------------------------------------------------------

PrefixInvariant == \A b \in Backups: SubSeq(logs[b], 1, Len(logs[primary])) = logs[primary]

Terminated == (Len(logs[primary]) = totalMsgs) /\ (\A b \in Backups: acks[b] = TRUE)
PostCondition == \A b \in Backups: logs[primary] = logs[b]

=============================================================================
\* Modification History
\* Last modified Sun May 21 16:34:58 EDT 2023 by 72jen
\* Created Thu May 18 14:14:02 EDT 2023 by 72jen


=============================================================================
\* Modification History
\* Created Thu May 18 15:16:08 EDT 2023 by 72jen
