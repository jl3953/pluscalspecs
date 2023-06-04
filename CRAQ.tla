-------------------------------- MODULE CRAQ --------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Clients, Nodes, head, tail, NumMsgs, Objects

\*NumMsgs == NumWrites + NumReads

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

READ == TRUE
WRITE == ~READ
Actions == {READ, WRITE}



OperationType == [obj: Objects, uniqueId: UniqueIds, action: Actions]
LogEntryType == [uniqueId: UniqueIds, isDirty: {TRUE, FALSE}]


\*NotObject == CHOOSE o : ~(o \in Objects)
\*NotClient == CHOOSE c : ~(c \in Clients)


(****************************************************************************

--fair algorithm CRAQ {

        \* declaration of global variables
        variables   msgQs = [e \in Network |-> << >>],
                    allObjLogs = [n \in Nodes |-> [o \in Objects |-> << >>] ],
                    clientOpSet = {},
                    totalOrder = [o \in Objects |-> << >>];
        
        \* operator definitions
        define {
            
            PotentialRequestClients(n) == IF n = head THEN Clients ELSE {Predecessors[n]} \cup Clients

            readObjFromSelf(objLogs, obj) == LET log == objLogs[obj] IN
                                                IF log = << >> THEN [   obj |-> obj,
                                                                        uniqueId |-> <<CHOOSE cl \in Clients: TRUE, 0>>,
                                                                        action |-> READ]
                                                    ELSE [  obj |-> obj, 
                                                            uniqueId |-> Head(objLogs[obj]).uniqueId, 
                                                            action |-> WRITE]
                                                            
            isDirtyVersion(objLogs, obj) == Head(objLogs[obj]).isDirty
            
            defaultOp == CHOOSE op \in OperationType : TRUE
            defaultSrcDestNode == CHOOSE node \in Nodes \cup Clients : TRUE
            defaultClient == CHOOSE client \in Clients : TRUE
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
        macro dirtyWriteObj(objLogs, obj, uniqueId) {
            objLogs[obj] := Append(@, [uniqueId |-> uniqueId, isDirty |-> TRUE]);
        }
        macro applyDirtyWrite(objLogs, obj) {
            objLogs[obj] := Append(Tail(@), [Head(@) EXCEPT !.isDirty = TRUE]); 
        }
        
        \* procedures
        procedure query(src = defaultSrcDestNode, 
                        dest = defaultSrcDestNode, 
                        op_query = defaultOp, 
                        resp_query = defaultOp) {
            sendQuery: send(<<src, dest>>, op_query);
            rcvResp: rcv(<<dest, src>>, resp_query);
            ret: return;
        }
    
    \* algorithm body or process declarations  
    
    
    \* Every client will simply send three write operations to every object
    \* to the head.                  
    fair process(client \in Clients) 
        variables   sequencer = 1,
                    objects = Objects,
                    obj = defaultOp, resp_c = defaultOp, op_c = defaultOp;
    {
        newMsg: while (sequencer <= NumMsgs) {
            newObj: while (objects /= {}) {
                obj := CHOOSE o \in objects : TRUE; 
                op_c := [   obj |-> obj,
                            uniqueId |-> <<self, sequencer>>,
                            action |-> WRITE];
                call query(self, head, op_c, resp_c);
                decrement: objects := @ \ {obj};
            };
            
            increment: 
            sequencer := @ + 1;
            clientOpSet := clientOpSet \cup {op_c};
            objects := Objects;
        }
    }

    fair process (headProcess="head") 
        variables   succ_h = Successors[head],
                    op_h = defaultOp, resp_h = defaultOp, requester_h = defaultClient; 
    {
        listen_head: 
        while (TRUE) {
        
            with (temp \in {c \in PotentialRequestClients(head): msgQs[<<c, head>>] /= << >>}) {
                requester_h := temp;
            };
                                                       
            incomingClientReq_h: 
            rcv(<<requester_h, head>>, op_h); 
            if (op_h.action = READ) {
            
                readingObj_h: if (isDirtyVersion(allObjLogs[head], op_h.obj)) {
                    call query(head, tail, op_h, resp_h);
                } else {    
                    resp_h := readObjFromSelf(allObjLogs[head], op_h.obj);
                };
                
                respondTorequester_h: send(<<head, requester_h>>, resp_h);
                
            } else {
                    
                dirtyWrite_h: dirtyWriteObj(allObjLogs[head], op_h.obj, op_h.uniqueId);
                    
                propagate_h: send(<<head, succ_h>>, op_h);
                    
                recvAck_h: rcv(<<succ_h, head>>, resp_h);
                    
                applyWrite_h: applyDirtyWrite(allObjLogs[head], op_h.obj);
                                 
                ackSuccessfulWrite_h: resp_h := [   obj |-> op_h.obj,
                                                    uniqueId |-> op_h.uniqueId,
                                                    action |-> TRUE];
                send(<<head, requester_h>>, resp_h);                                        
            }
        }
    }
    
    fair process (tailProcess="tail") 
        variables   op_t = defaultOp, resp_t = defaultOp, 
                    requester_t = defaultSrcDestNode;
    {
        listen_t: while (TRUE) {
        
            with (temp \in {n \in PotentialRequestClients(tail) : msgQs[<<n, tail>>] /= << >>}) {
                requester_t := temp;
            };
            
            incomingReq_t:
            rcv(<<requester_t, tail>>, op_t); 
            if (op_t.action = READ) {
                readObj_t: resp_t := readObjFromSelf(allObjLogs[tail], op_t.obj); 
                
                respond_t: send(<<tail, requester_t>>, resp_t);
                 
            } else {
            
                applyWrite_t: allObjLogs[tail][op_t.obj] := Append(allObjLogs[tail][op_t.obj], 
                                          [uniqueId |-> op_t.uniqueId, isDirty |-> FALSE]);
                                 
                ackSuccessfulWrite_t: resp_t := [  obj |-> op_t.obj,
                                                uniqueId |-> op_t.uniqueId,
                                                action |-> TRUE];
                send(<<tail, requester_t>>, resp_t);     
            }; 
            
            totallyOrder: totalOrder[op_t.obj] := Append(@, op_t);
        }
    }
    
    fair process (n \in Nodes \ {head, tail})
        variables   prev = Predecessors[self],
                    succ = Successors[self],
                    op = defaultOp, resp = defaultOp, requester = defaultSrcDestNode; 
    {
        listen: while (TRUE) {
        
            with (temp \in {n \in PotentialRequestClients(self) : msgQs[<<n, self>>] /= << >>}) {
                requester := temp;
            };
            
            incomingReq: 
            rcv(<<requester, self>>, op); 
            if (op.action = READ) {
            
                readingObj: if (isDirtyVersion(allObjLogs[self], op.obj)) {
                    call query(self, tail, op, resp);
                } else {    
                    resp := readObjFromSelf(allObjLogs[self], op.obj);
                };
                
                respondToClient: send(<<self, requester>>, resp);
            } else {
                dirtyWrite: dirtyWriteObj(allObjLogs[self], op.obj, op.uniqueId);
                    
                propagate: send(<<self, succ>>, op);
                    
                recvAck: rcv(<<succ, self>>, resp);
                    
                applyWrite: applyDirtyWrite(allObjLogs[self], op.obj);
                                 
                ackSuccessfulWrite: resp := [   obj |-> op.obj,
                                                uniqueId |-> op.uniqueId,
                                                action |-> TRUE];
                send(<<self, prev>>, resp); 
            }
        }  
    }
}
****************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "97233a0d" /\ chksum(tla) = "a8d45b4f")
VARIABLES msgQs, allObjLogs, clientOpSet, totalOrder, pc, stack

(* define statement *)
PotentialRequestClients(n) == IF n = head THEN Clients ELSE {Predecessors[n]} \cup Clients

readObjFromSelf(objLogs, obj) == LET log == objLogs[obj] IN
                                    IF log = << >> THEN [   obj |-> obj,
                                                            uniqueId |-> <<CHOOSE cl \in Clients: TRUE, 0>>,
                                                            action |-> READ]
                                        ELSE [  obj |-> obj,
                                                uniqueId |-> Head(objLogs[obj]).uniqueId,
                                                action |-> WRITE]

isDirtyVersion(objLogs, obj) == Head(objLogs[obj]).isDirty

defaultOp == CHOOSE op \in OperationType : TRUE
defaultSrcDestNode == CHOOSE node \in Nodes \cup Clients : TRUE
defaultClient == CHOOSE client \in Clients : TRUE

VARIABLES src, dest, op_query, resp_query, sequencer, objects, obj, resp_c, 
          op_c, succ_h, op_h, resp_h, requester_h, op_t, resp_t, requester_t, 
          prev, succ, op, resp, requester

vars == << msgQs, allObjLogs, clientOpSet, totalOrder, pc, stack, src, dest, 
           op_query, resp_query, sequencer, objects, obj, resp_c, op_c, 
           succ_h, op_h, resp_h, requester_h, op_t, resp_t, requester_t, prev, 
           succ, op, resp, requester >>

ProcSet == (Clients) \cup {"head"} \cup {"tail"} \cup (Nodes \ {head, tail})

Init == (* Global variables *)
        /\ msgQs = [e \in Network |-> << >>]
        /\ allObjLogs = [n \in Nodes |-> [o \in Objects |-> << >>] ]
        /\ clientOpSet = {}
        /\ totalOrder = [o \in Objects |-> << >>]
        (* Procedure query *)
        /\ src = [ self \in ProcSet |-> defaultSrcDestNode]
        /\ dest = [ self \in ProcSet |-> defaultSrcDestNode]
        /\ op_query = [ self \in ProcSet |-> defaultOp]
        /\ resp_query = [ self \in ProcSet |-> defaultOp]
        (* Process client *)
        /\ sequencer = [self \in Clients |-> 1]
        /\ objects = [self \in Clients |-> Objects]
        /\ obj = [self \in Clients |-> defaultOp]
        /\ resp_c = [self \in Clients |-> defaultOp]
        /\ op_c = [self \in Clients |-> defaultOp]
        (* Process headProcess *)
        /\ succ_h = Successors[head]
        /\ op_h = defaultOp
        /\ resp_h = defaultOp
        /\ requester_h = defaultClient
        (* Process tailProcess *)
        /\ op_t = defaultOp
        /\ resp_t = defaultOp
        /\ requester_t = defaultSrcDestNode
        (* Process n *)
        /\ prev = [self \in Nodes \ {head, tail} |-> Predecessors[self]]
        /\ succ = [self \in Nodes \ {head, tail} |-> Successors[self]]
        /\ op = [self \in Nodes \ {head, tail} |-> defaultOp]
        /\ resp = [self \in Nodes \ {head, tail} |-> defaultOp]
        /\ requester = [self \in Nodes \ {head, tail} |-> defaultSrcDestNode]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "newMsg"
                                        [] self = "head" -> "listen_head"
                                        [] self = "tail" -> "listen_t"
                                        [] self \in Nodes \ {head, tail} -> "listen"]

sendQuery(self) == /\ pc[self] = "sendQuery"
                   /\ msgQs' = [msgQs EXCEPT ![(<<src[self], dest[self]>>)] = Append(@, op_query[self])]
                   /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                   /\ UNCHANGED << allObjLogs, clientOpSet, totalOrder, stack, 
                                   src, dest, op_query, resp_query, sequencer, 
                                   objects, obj, resp_c, op_c, succ_h, op_h, 
                                   resp_h, requester_h, op_t, resp_t, 
                                   requester_t, prev, succ, op, resp, 
                                   requester >>

rcvResp(self) == /\ pc[self] = "rcvResp"
                 /\ msgQs[(<<dest[self], src[self]>>)] /= << >>
                 /\ resp_query' = [resp_query EXCEPT ![self] = Head(msgQs[(<<dest[self], src[self]>>)])]
                 /\ msgQs' = [msgQs EXCEPT ![(<<dest[self], src[self]>>)] = Tail(@)]
                 /\ pc' = [pc EXCEPT ![self] = "ret"]
                 /\ UNCHANGED << allObjLogs, clientOpSet, totalOrder, stack, 
                                 src, dest, op_query, sequencer, objects, obj, 
                                 resp_c, op_c, succ_h, op_h, resp_h, 
                                 requester_h, op_t, resp_t, requester_t, prev, 
                                 succ, op, resp, requester >>

ret(self) == /\ pc[self] = "ret"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ src' = [src EXCEPT ![self] = Head(stack[self]).src]
             /\ dest' = [dest EXCEPT ![self] = Head(stack[self]).dest]
             /\ op_query' = [op_query EXCEPT ![self] = Head(stack[self]).op_query]
             /\ resp_query' = [resp_query EXCEPT ![self] = Head(stack[self]).resp_query]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << msgQs, allObjLogs, clientOpSet, totalOrder, 
                             sequencer, objects, obj, resp_c, op_c, succ_h, 
                             op_h, resp_h, requester_h, op_t, resp_t, 
                             requester_t, prev, succ, op, resp, requester >>

query(self) == sendQuery(self) \/ rcvResp(self) \/ ret(self)

newMsg(self) == /\ pc[self] = "newMsg"
                /\ IF sequencer[self] <= NumMsgs
                      THEN /\ pc' = [pc EXCEPT ![self] = "newObj"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << msgQs, allObjLogs, clientOpSet, totalOrder, 
                                stack, src, dest, op_query, resp_query, 
                                sequencer, objects, obj, resp_c, op_c, succ_h, 
                                op_h, resp_h, requester_h, op_t, resp_t, 
                                requester_t, prev, succ, op, resp, requester >>

newObj(self) == /\ pc[self] = "newObj"
                /\ IF objects[self] /= {}
                      THEN /\ obj' = [obj EXCEPT ![self] = CHOOSE o \in objects[self] : TRUE]
                           /\ op_c' = [op_c EXCEPT ![self] = [   obj |-> obj'[self],
                                                                 uniqueId |-> <<self, sequencer[self]>>,
                                                                 action |-> WRITE]]
                           /\ /\ dest' = [dest EXCEPT ![self] = head]
                              /\ op_query' = [op_query EXCEPT ![self] = op_c'[self]]
                              /\ resp_query' = [resp_query EXCEPT ![self] = resp_c[self]]
                              /\ src' = [src EXCEPT ![self] = self]
                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "query",
                                                                       pc        |->  "decrement",
                                                                       src       |->  src[self],
                                                                       dest      |->  dest[self],
                                                                       op_query  |->  op_query[self],
                                                                       resp_query |->  resp_query[self] ] >>
                                                                   \o stack[self]]
                           /\ pc' = [pc EXCEPT ![self] = "sendQuery"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "increment"]
                           /\ UNCHANGED << stack, src, dest, op_query, 
                                           resp_query, obj, op_c >>
                /\ UNCHANGED << msgQs, allObjLogs, clientOpSet, totalOrder, 
                                sequencer, objects, resp_c, succ_h, op_h, 
                                resp_h, requester_h, op_t, resp_t, requester_t, 
                                prev, succ, op, resp, requester >>

decrement(self) == /\ pc[self] = "decrement"
                   /\ objects' = [objects EXCEPT ![self] = @ \ {obj[self]}]
                   /\ pc' = [pc EXCEPT ![self] = "newObj"]
                   /\ UNCHANGED << msgQs, allObjLogs, clientOpSet, totalOrder, 
                                   stack, src, dest, op_query, resp_query, 
                                   sequencer, obj, resp_c, op_c, succ_h, op_h, 
                                   resp_h, requester_h, op_t, resp_t, 
                                   requester_t, prev, succ, op, resp, 
                                   requester >>

increment(self) == /\ pc[self] = "increment"
                   /\ sequencer' = [sequencer EXCEPT ![self] = @ + 1]
                   /\ clientOpSet' = (clientOpSet \cup {op_c[self]})
                   /\ objects' = [objects EXCEPT ![self] = Objects]
                   /\ pc' = [pc EXCEPT ![self] = "newMsg"]
                   /\ UNCHANGED << msgQs, allObjLogs, totalOrder, stack, src, 
                                   dest, op_query, resp_query, obj, resp_c, 
                                   op_c, succ_h, op_h, resp_h, requester_h, 
                                   op_t, resp_t, requester_t, prev, succ, op, 
                                   resp, requester >>

client(self) == newMsg(self) \/ newObj(self) \/ decrement(self)
                   \/ increment(self)

listen_head == /\ pc["head"] = "listen_head"
               /\ \E temp \in {c \in PotentialRequestClients(head): msgQs[<<c, head>>] /= << >>}:
                    requester_h' = temp
               /\ pc' = [pc EXCEPT !["head"] = "incomingClientReq_h"]
               /\ UNCHANGED << msgQs, allObjLogs, clientOpSet, totalOrder, 
                               stack, src, dest, op_query, resp_query, 
                               sequencer, objects, obj, resp_c, op_c, succ_h, 
                               op_h, resp_h, op_t, resp_t, requester_t, prev, 
                               succ, op, resp, requester >>

incomingClientReq_h == /\ pc["head"] = "incomingClientReq_h"
                       /\ msgQs[(<<requester_h, head>>)] /= << >>
                       /\ op_h' = Head(msgQs[(<<requester_h, head>>)])
                       /\ msgQs' = [msgQs EXCEPT ![(<<requester_h, head>>)] = Tail(@)]
                       /\ IF op_h'.action = READ
                             THEN /\ pc' = [pc EXCEPT !["head"] = "readingObj_h"]
                             ELSE /\ pc' = [pc EXCEPT !["head"] = "dirtyWrite_h"]
                       /\ UNCHANGED << allObjLogs, clientOpSet, totalOrder, 
                                       stack, src, dest, op_query, resp_query, 
                                       sequencer, objects, obj, resp_c, op_c, 
                                       succ_h, resp_h, requester_h, op_t, 
                                       resp_t, requester_t, prev, succ, op, 
                                       resp, requester >>

readingObj_h == /\ pc["head"] = "readingObj_h"
                /\ IF isDirtyVersion(allObjLogs[head], op_h.obj)
                      THEN /\ /\ dest' = [dest EXCEPT !["head"] = tail]
                              /\ op_query' = [op_query EXCEPT !["head"] = op_h]
                              /\ resp_query' = [resp_query EXCEPT !["head"] = resp_h]
                              /\ src' = [src EXCEPT !["head"] = head]
                              /\ stack' = [stack EXCEPT !["head"] = << [ procedure |->  "query",
                                                                         pc        |->  "respondTorequester_h",
                                                                         src       |->  src["head"],
                                                                         dest      |->  dest["head"],
                                                                         op_query  |->  op_query["head"],
                                                                         resp_query |->  resp_query["head"] ] >>
                                                                     \o stack["head"]]
                           /\ pc' = [pc EXCEPT !["head"] = "sendQuery"]
                           /\ UNCHANGED resp_h
                      ELSE /\ resp_h' = readObjFromSelf(allObjLogs[head], op_h.obj)
                           /\ pc' = [pc EXCEPT !["head"] = "respondTorequester_h"]
                           /\ UNCHANGED << stack, src, dest, op_query, 
                                           resp_query >>
                /\ UNCHANGED << msgQs, allObjLogs, clientOpSet, totalOrder, 
                                sequencer, objects, obj, resp_c, op_c, succ_h, 
                                op_h, requester_h, op_t, resp_t, requester_t, 
                                prev, succ, op, resp, requester >>

respondTorequester_h == /\ pc["head"] = "respondTorequester_h"
                        /\ msgQs' = [msgQs EXCEPT ![(<<head, requester_h>>)] = Append(@, resp_h)]
                        /\ pc' = [pc EXCEPT !["head"] = "listen_head"]
                        /\ UNCHANGED << allObjLogs, clientOpSet, totalOrder, 
                                        stack, src, dest, op_query, resp_query, 
                                        sequencer, objects, obj, resp_c, op_c, 
                                        succ_h, op_h, resp_h, requester_h, 
                                        op_t, resp_t, requester_t, prev, succ, 
                                        op, resp, requester >>

dirtyWrite_h == /\ pc["head"] = "dirtyWrite_h"
                /\ allObjLogs' = [allObjLogs EXCEPT ![head][(op_h.obj)] = Append(@, [uniqueId |-> (op_h.uniqueId), isDirty |-> TRUE])]
                /\ pc' = [pc EXCEPT !["head"] = "propagate_h"]
                /\ UNCHANGED << msgQs, clientOpSet, totalOrder, stack, src, 
                                dest, op_query, resp_query, sequencer, objects, 
                                obj, resp_c, op_c, succ_h, op_h, resp_h, 
                                requester_h, op_t, resp_t, requester_t, prev, 
                                succ, op, resp, requester >>

propagate_h == /\ pc["head"] = "propagate_h"
               /\ msgQs' = [msgQs EXCEPT ![(<<head, succ_h>>)] = Append(@, op_h)]
               /\ pc' = [pc EXCEPT !["head"] = "recvAck_h"]
               /\ UNCHANGED << allObjLogs, clientOpSet, totalOrder, stack, src, 
                               dest, op_query, resp_query, sequencer, objects, 
                               obj, resp_c, op_c, succ_h, op_h, resp_h, 
                               requester_h, op_t, resp_t, requester_t, prev, 
                               succ, op, resp, requester >>

recvAck_h == /\ pc["head"] = "recvAck_h"
             /\ msgQs[(<<succ_h, head>>)] /= << >>
             /\ resp_h' = Head(msgQs[(<<succ_h, head>>)])
             /\ msgQs' = [msgQs EXCEPT ![(<<succ_h, head>>)] = Tail(@)]
             /\ pc' = [pc EXCEPT !["head"] = "applyWrite_h"]
             /\ UNCHANGED << allObjLogs, clientOpSet, totalOrder, stack, src, 
                             dest, op_query, resp_query, sequencer, objects, 
                             obj, resp_c, op_c, succ_h, op_h, requester_h, 
                             op_t, resp_t, requester_t, prev, succ, op, resp, 
                             requester >>

applyWrite_h == /\ pc["head"] = "applyWrite_h"
                /\ allObjLogs' = [allObjLogs EXCEPT ![head][(op_h.obj)] = Append(Tail(@), [Head(@) EXCEPT !.isDirty = TRUE])]
                /\ pc' = [pc EXCEPT !["head"] = "ackSuccessfulWrite_h"]
                /\ UNCHANGED << msgQs, clientOpSet, totalOrder, stack, src, 
                                dest, op_query, resp_query, sequencer, objects, 
                                obj, resp_c, op_c, succ_h, op_h, resp_h, 
                                requester_h, op_t, resp_t, requester_t, prev, 
                                succ, op, resp, requester >>

ackSuccessfulWrite_h == /\ pc["head"] = "ackSuccessfulWrite_h"
                        /\ resp_h' = [   obj |-> op_h.obj,
                                         uniqueId |-> op_h.uniqueId,
                                         action |-> TRUE]
                        /\ msgQs' = [msgQs EXCEPT ![(<<head, requester_h>>)] = Append(@, resp_h')]
                        /\ pc' = [pc EXCEPT !["head"] = "listen_head"]
                        /\ UNCHANGED << allObjLogs, clientOpSet, totalOrder, 
                                        stack, src, dest, op_query, resp_query, 
                                        sequencer, objects, obj, resp_c, op_c, 
                                        succ_h, op_h, requester_h, op_t, 
                                        resp_t, requester_t, prev, succ, op, 
                                        resp, requester >>

headProcess == listen_head \/ incomingClientReq_h \/ readingObj_h
                  \/ respondTorequester_h \/ dirtyWrite_h \/ propagate_h
                  \/ recvAck_h \/ applyWrite_h \/ ackSuccessfulWrite_h

listen_t == /\ pc["tail"] = "listen_t"
            /\ \E temp \in {n \in PotentialRequestClients(tail) : msgQs[<<n, tail>>] /= << >>}:
                 requester_t' = temp
            /\ pc' = [pc EXCEPT !["tail"] = "incomingReq_t"]
            /\ UNCHANGED << msgQs, allObjLogs, clientOpSet, totalOrder, stack, 
                            src, dest, op_query, resp_query, sequencer, 
                            objects, obj, resp_c, op_c, succ_h, op_h, resp_h, 
                            requester_h, op_t, resp_t, prev, succ, op, resp, 
                            requester >>

incomingReq_t == /\ pc["tail"] = "incomingReq_t"
                 /\ msgQs[(<<requester_t, tail>>)] /= << >>
                 /\ op_t' = Head(msgQs[(<<requester_t, tail>>)])
                 /\ msgQs' = [msgQs EXCEPT ![(<<requester_t, tail>>)] = Tail(@)]
                 /\ IF op_t'.action = READ
                       THEN /\ pc' = [pc EXCEPT !["tail"] = "readObj_t"]
                       ELSE /\ pc' = [pc EXCEPT !["tail"] = "applyWrite_t"]
                 /\ UNCHANGED << allObjLogs, clientOpSet, totalOrder, stack, 
                                 src, dest, op_query, resp_query, sequencer, 
                                 objects, obj, resp_c, op_c, succ_h, op_h, 
                                 resp_h, requester_h, resp_t, requester_t, 
                                 prev, succ, op, resp, requester >>

readObj_t == /\ pc["tail"] = "readObj_t"
             /\ resp_t' = readObjFromSelf(allObjLogs[tail], op_t.obj)
             /\ pc' = [pc EXCEPT !["tail"] = "respond_t"]
             /\ UNCHANGED << msgQs, allObjLogs, clientOpSet, totalOrder, stack, 
                             src, dest, op_query, resp_query, sequencer, 
                             objects, obj, resp_c, op_c, succ_h, op_h, resp_h, 
                             requester_h, op_t, requester_t, prev, succ, op, 
                             resp, requester >>

respond_t == /\ pc["tail"] = "respond_t"
             /\ msgQs' = [msgQs EXCEPT ![(<<tail, requester_t>>)] = Append(@, resp_t)]
             /\ pc' = [pc EXCEPT !["tail"] = "totallyOrder"]
             /\ UNCHANGED << allObjLogs, clientOpSet, totalOrder, stack, src, 
                             dest, op_query, resp_query, sequencer, objects, 
                             obj, resp_c, op_c, succ_h, op_h, resp_h, 
                             requester_h, op_t, resp_t, requester_t, prev, 
                             succ, op, resp, requester >>

applyWrite_t == /\ pc["tail"] = "applyWrite_t"
                /\ allObjLogs' = [allObjLogs EXCEPT ![tail][op_t.obj] =                   Append(allObjLogs[tail][op_t.obj],
                                                                        [uniqueId |-> op_t.uniqueId, isDirty |-> FALSE])]
                /\ pc' = [pc EXCEPT !["tail"] = "ackSuccessfulWrite_t"]
                /\ UNCHANGED << msgQs, clientOpSet, totalOrder, stack, src, 
                                dest, op_query, resp_query, sequencer, objects, 
                                obj, resp_c, op_c, succ_h, op_h, resp_h, 
                                requester_h, op_t, resp_t, requester_t, prev, 
                                succ, op, resp, requester >>

ackSuccessfulWrite_t == /\ pc["tail"] = "ackSuccessfulWrite_t"
                        /\ resp_t' = [  obj |-> op_t.obj,
                                     uniqueId |-> op_t.uniqueId,
                                     action |-> TRUE]
                        /\ msgQs' = [msgQs EXCEPT ![(<<tail, requester_t>>)] = Append(@, resp_t')]
                        /\ pc' = [pc EXCEPT !["tail"] = "totallyOrder"]
                        /\ UNCHANGED << allObjLogs, clientOpSet, totalOrder, 
                                        stack, src, dest, op_query, resp_query, 
                                        sequencer, objects, obj, resp_c, op_c, 
                                        succ_h, op_h, resp_h, requester_h, 
                                        op_t, requester_t, prev, succ, op, 
                                        resp, requester >>

totallyOrder == /\ pc["tail"] = "totallyOrder"
                /\ totalOrder' = [totalOrder EXCEPT ![op_t.obj] = Append(@, op_t)]
                /\ pc' = [pc EXCEPT !["tail"] = "listen_t"]
                /\ UNCHANGED << msgQs, allObjLogs, clientOpSet, stack, src, 
                                dest, op_query, resp_query, sequencer, objects, 
                                obj, resp_c, op_c, succ_h, op_h, resp_h, 
                                requester_h, op_t, resp_t, requester_t, prev, 
                                succ, op, resp, requester >>

tailProcess == listen_t \/ incomingReq_t \/ readObj_t \/ respond_t
                  \/ applyWrite_t \/ ackSuccessfulWrite_t \/ totallyOrder

listen(self) == /\ pc[self] = "listen"
                /\ \E temp \in {n \in PotentialRequestClients(self) : msgQs[<<n, self>>] /= << >>}:
                     requester' = [requester EXCEPT ![self] = temp]
                /\ pc' = [pc EXCEPT ![self] = "incomingReq"]
                /\ UNCHANGED << msgQs, allObjLogs, clientOpSet, totalOrder, 
                                stack, src, dest, op_query, resp_query, 
                                sequencer, objects, obj, resp_c, op_c, succ_h, 
                                op_h, resp_h, requester_h, op_t, resp_t, 
                                requester_t, prev, succ, op, resp >>

incomingReq(self) == /\ pc[self] = "incomingReq"
                     /\ msgQs[(<<requester[self], self>>)] /= << >>
                     /\ op' = [op EXCEPT ![self] = Head(msgQs[(<<requester[self], self>>)])]
                     /\ msgQs' = [msgQs EXCEPT ![(<<requester[self], self>>)] = Tail(@)]
                     /\ IF op'[self].action = READ
                           THEN /\ pc' = [pc EXCEPT ![self] = "readingObj"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "dirtyWrite"]
                     /\ UNCHANGED << allObjLogs, clientOpSet, totalOrder, 
                                     stack, src, dest, op_query, resp_query, 
                                     sequencer, objects, obj, resp_c, op_c, 
                                     succ_h, op_h, resp_h, requester_h, op_t, 
                                     resp_t, requester_t, prev, succ, resp, 
                                     requester >>

readingObj(self) == /\ pc[self] = "readingObj"
                    /\ IF isDirtyVersion(allObjLogs[self], op[self].obj)
                          THEN /\ /\ dest' = [dest EXCEPT ![self] = tail]
                                  /\ op_query' = [op_query EXCEPT ![self] = op[self]]
                                  /\ resp_query' = [resp_query EXCEPT ![self] = resp[self]]
                                  /\ src' = [src EXCEPT ![self] = self]
                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "query",
                                                                           pc        |->  "respondToClient",
                                                                           src       |->  src[self],
                                                                           dest      |->  dest[self],
                                                                           op_query  |->  op_query[self],
                                                                           resp_query |->  resp_query[self] ] >>
                                                                       \o stack[self]]
                               /\ pc' = [pc EXCEPT ![self] = "sendQuery"]
                               /\ resp' = resp
                          ELSE /\ resp' = [resp EXCEPT ![self] = readObjFromSelf(allObjLogs[self], op[self].obj)]
                               /\ pc' = [pc EXCEPT ![self] = "respondToClient"]
                               /\ UNCHANGED << stack, src, dest, op_query, 
                                               resp_query >>
                    /\ UNCHANGED << msgQs, allObjLogs, clientOpSet, totalOrder, 
                                    sequencer, objects, obj, resp_c, op_c, 
                                    succ_h, op_h, resp_h, requester_h, op_t, 
                                    resp_t, requester_t, prev, succ, op, 
                                    requester >>

respondToClient(self) == /\ pc[self] = "respondToClient"
                         /\ msgQs' = [msgQs EXCEPT ![(<<self, requester[self]>>)] = Append(@, resp[self])]
                         /\ pc' = [pc EXCEPT ![self] = "listen"]
                         /\ UNCHANGED << allObjLogs, clientOpSet, totalOrder, 
                                         stack, src, dest, op_query, 
                                         resp_query, sequencer, objects, obj, 
                                         resp_c, op_c, succ_h, op_h, resp_h, 
                                         requester_h, op_t, resp_t, 
                                         requester_t, prev, succ, op, resp, 
                                         requester >>

dirtyWrite(self) == /\ pc[self] = "dirtyWrite"
                    /\ allObjLogs' = [allObjLogs EXCEPT ![self][(op[self].obj)] = Append(@, [uniqueId |-> (op[self].uniqueId), isDirty |-> TRUE])]
                    /\ pc' = [pc EXCEPT ![self] = "propagate"]
                    /\ UNCHANGED << msgQs, clientOpSet, totalOrder, stack, src, 
                                    dest, op_query, resp_query, sequencer, 
                                    objects, obj, resp_c, op_c, succ_h, op_h, 
                                    resp_h, requester_h, op_t, resp_t, 
                                    requester_t, prev, succ, op, resp, 
                                    requester >>

propagate(self) == /\ pc[self] = "propagate"
                   /\ msgQs' = [msgQs EXCEPT ![(<<self, succ[self]>>)] = Append(@, op[self])]
                   /\ pc' = [pc EXCEPT ![self] = "recvAck"]
                   /\ UNCHANGED << allObjLogs, clientOpSet, totalOrder, stack, 
                                   src, dest, op_query, resp_query, sequencer, 
                                   objects, obj, resp_c, op_c, succ_h, op_h, 
                                   resp_h, requester_h, op_t, resp_t, 
                                   requester_t, prev, succ, op, resp, 
                                   requester >>

recvAck(self) == /\ pc[self] = "recvAck"
                 /\ msgQs[(<<succ[self], self>>)] /= << >>
                 /\ resp' = [resp EXCEPT ![self] = Head(msgQs[(<<succ[self], self>>)])]
                 /\ msgQs' = [msgQs EXCEPT ![(<<succ[self], self>>)] = Tail(@)]
                 /\ pc' = [pc EXCEPT ![self] = "applyWrite"]
                 /\ UNCHANGED << allObjLogs, clientOpSet, totalOrder, stack, 
                                 src, dest, op_query, resp_query, sequencer, 
                                 objects, obj, resp_c, op_c, succ_h, op_h, 
                                 resp_h, requester_h, op_t, resp_t, 
                                 requester_t, prev, succ, op, requester >>

applyWrite(self) == /\ pc[self] = "applyWrite"
                    /\ allObjLogs' = [allObjLogs EXCEPT ![self][(op[self].obj)] = Append(Tail(@), [Head(@) EXCEPT !.isDirty = TRUE])]
                    /\ pc' = [pc EXCEPT ![self] = "ackSuccessfulWrite"]
                    /\ UNCHANGED << msgQs, clientOpSet, totalOrder, stack, src, 
                                    dest, op_query, resp_query, sequencer, 
                                    objects, obj, resp_c, op_c, succ_h, op_h, 
                                    resp_h, requester_h, op_t, resp_t, 
                                    requester_t, prev, succ, op, resp, 
                                    requester >>

ackSuccessfulWrite(self) == /\ pc[self] = "ackSuccessfulWrite"
                            /\ resp' = [resp EXCEPT ![self] = [   obj |-> op[self].obj,
                                                                  uniqueId |-> op[self].uniqueId,
                                                                  action |-> TRUE]]
                            /\ msgQs' = [msgQs EXCEPT ![(<<self, prev[self]>>)] = Append(@, resp'[self])]
                            /\ pc' = [pc EXCEPT ![self] = "listen"]
                            /\ UNCHANGED << allObjLogs, clientOpSet, 
                                            totalOrder, stack, src, dest, 
                                            op_query, resp_query, sequencer, 
                                            objects, obj, resp_c, op_c, succ_h, 
                                            op_h, resp_h, requester_h, op_t, 
                                            resp_t, requester_t, prev, succ, 
                                            op, requester >>

n(self) == listen(self) \/ incomingReq(self) \/ readingObj(self)
              \/ respondToClient(self) \/ dirtyWrite(self)
              \/ propagate(self) \/ recvAck(self) \/ applyWrite(self)
              \/ ackSuccessfulWrite(self)

Next == headProcess \/ tailProcess
           \/ (\E self \in ProcSet: query(self))
           \/ (\E self \in Clients: client(self))
           \/ (\E self \in Nodes \ {head, tail}: n(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in Clients : WF_vars(client(self)) /\ WF_vars(query(self))
        /\ WF_vars(headProcess) /\ WF_vars(query("head"))
        /\ WF_vars(tailProcess)
        /\ \A self \in Nodes \ {head, tail} : WF_vars(n(self)) /\ WF_vars(query(self))

\* END TRANSLATION 





TypeInvariant  ==   /\ msgQs        \in [Network -> {<< >>} \cup Seq(OperationType)]
                    /\ allObjLogs   \in [Nodes -> [Objects -> {<< >>} \cup Seq(LogEntryType)]]
                    /\ totalOrder   \in [Objects -> {<< >>} \cup Seq(OperationType)]
                    /\ succ_h       = Successors[head]
                    /\ op_h         \in OperationType
                    /\ resp_h       \in OperationType
                    /\ requester_h  \in Clients
                    /\ succ         \in [Nodes \ {head, tail} -> Nodes \ {head}]
                    /\ prev         \in [Nodes \ {head, tail} -> Nodes \ {tail}]
                    /\ op           \in [Nodes \ {head, tail} -> OperationType]
                    /\ resp         \in [Nodes \ {head, tail} -> OperationType]
                    /\ requester    \in [Nodes \ {head, tail} -> Clients \cup (Nodes \ {tail})]   
                    /\ resp_t       \in OperationType
                    /\ op_t         \in OperationType
                    /\ requester_t  \in Clients \cup (Nodes \ {tail})
                    

RECURSIVE clean(_)
clean(log) == IF log = << >> \/ ~Head(log).isDirty THEN log ELSE clean(Tail(log))

Terminated == \A o \in Objects : LET headLog == allObjLogs[head][o]
                                    IN  /\ headLog = clean(headLog) 
                                        /\ Len(headLog) = NumMsgs
                                    
PostCondition == \A node \in Nodes \ {tail}: \A o \in Objects : 
                    LET log == allObjLogs[node][o]
                        tailLog == allObjLogs[tail][o] IN log = tailLog
                  
                  
\*RECURSIVE SeqToSet(_, _)
\*SeqToSet(seq, set) == IF seq = << >> 
\*                        THEN set 
\*                        ELSE SeqToSet(Tail(seq), set \cup {Head(seq)})  
\*unorderedOpsByObj == [o \in Objects |-> SeqToSet(totalOrder[o], {})]

Map(s, f(_)) == [i \in s |-> f(i)]

RECURSIVE ReduceSeq(_, _, _)
ReduceSeq(seq, f(_, _), e) == IF seq = << >> THEN e 
                                ELSE f(Head(seq), ReduceSeq(Tail(seq), f, e))
RECURSIVE ReduceSet(_, _, _)
ReduceSet(set, f(_, _), e) == IF set = {} THEN e ELSE 
                            LET chosen == CHOOSE rand \in set: TRUE 
                            IN f(chosen, ReduceSet(set \ {chosen}, f, e))

seqOfAllSeenOps == LET concat(seq1, seq2) == seq1 \o seq2 
                    IN ReduceSet(Objects, concat, << >>)
                    
setOfAllSeenOps == LET add(item, set) == set \cup {item} 
                    IN ReduceSeq(seqOfAllSeenOps, add, {})
                               
TotalOrderExists ==     /\ Len(seqOfAllSeenOps) = Cardinality(clientOpSet)
                        /\ \A o \in clientOpSet: o \in setOfAllSeenOps

IsPrefix(prefixParam, logParam) == LET prefix == clean(prefixParam) 
                                       log == clean(logParam) IN    CASE prefix = << >> -> TRUE 
                                                                    [] log = << >> -> FALSE
                                                                    [] OTHER -> SubSeq(log, 1, Len(prefix)) = prefix
  

PrefixInvariant == \A node \in Nodes \ {tail}: \A o \in Objects: 
                        LET successor == Successors[node] IN IsPrefix(allObjLogs[node][o], allObjLogs[succ][o])
=============================================================================
\* Modification History
\* Last modified Sun Jun 04 01:30:30 EDT 2023 by jenniferlam
\* Last modified Fri Jun 02 18:58:13 EDT 2023 by 72jen
\* Created Thu May 25 11:58:00 EDT 2023 by jenniferlam
