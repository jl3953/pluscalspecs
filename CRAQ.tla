-------------------------------- MODULE CRAQ --------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Clients, Nodes, head, tail, NumWrites, NumReads, Objects

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

READ == "READ"
WRITE == "WRITE"
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
            
            sendersTo(n) == IF n = head THEN Clients ELSE {Predecessors[n]} \cup Clients

            read(objLogs, obj) == LET log == objLogs[obj] IN
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
            objLogs[obj] := Append(Tail(@), [Head(@) EXCEPT !.isDirty = FALSE]); 
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
        newWrites: while (sequencer <= NumWrites) {
            newObj_w: while (objects /= {}) {
                obj := CHOOSE o \in objects : TRUE; 
                op_c := [   obj |-> obj,
                            uniqueId |-> <<self, sequencer>>,
                            action |-> WRITE];
                call query(self, head, op_c, resp_c);
                decrement_w: objects := @ \ {obj};
            };
            
            increment_w: 
            sequencer := @ + 1;
            clientOpSet := clientOpSet \cup {op_c};
            objects := Objects;
        };
        
        newReads: while (sequencer <= NumWrites + NumReads) {
            newObj_r: while (objects /= {}) {
                obj := CHOOSE o \in objects : TRUE; 
                op_c := [   obj |-> obj,
                            uniqueId |-> <<self, sequencer>>,
                            action |-> READ];
                call query(self, head, op_c, resp_c);
                decrement_r: objects := @ \ {obj};
            };
            
            increment_r: 
            sequencer := @ + 1;
            clientOpSet := clientOpSet \cup {op_c};
            objects := Objects;
        }
    }

    fair process (headProcess="head") 
        variables   succ_h = Successors[head],
                    op_h = defaultOp, resp_h = defaultOp, sender_h = defaultClient; 
    {
        listen_h: 
        while (TRUE) {
        
            
            with (temp \in {s \in sendersTo(head): msgQs[<<s, head>>] /= << >>}) {
                sender_h := temp;
            };
            
            incomingReq_h:                                           
            rcv(<<sender_h, head>>, op_h); 
            if (op_h.action = READ) {
            
                checkDirty_h: if (isDirtyVersion(allObjLogs[head], op_h.obj)) {
                    apportion_h: call query(head, tail, op_h, resp_h);
                } else {    
                    readFromSelf_h: 
                    resp_h := read(allObjLogs[head], op_h.obj);
                };
                
                replyToReadReq_h: send(<<head, sender_h>>, resp_h);
                
            } else {     
                dirtyWriteObj(allObjLogs[head], op_h.obj, op_h.uniqueId);
                    
                propagate_h: send(<<head, succ_h>>, op_h);
                    
                recvAck_h: rcv(<<succ_h, head>>, resp_h);  
                applyDirtyWrite(allObjLogs[head], op_h.obj);
                                 
                sendAck_h: send(<<head, sender_h>>, [   obj |-> op_h.obj,
                                                        uniqueId |-> op_h.uniqueId,
                                                        action |-> WRITE]);                                        
            }
        }
    }
    
    fair process (tailProcess="tail") 
        variables   op_t = defaultOp, resp_t = defaultOp, 
                    sender_t = defaultSrcDestNode;
    {
        listen_t: while (TRUE) {
            
            
            with (temp \in {s \in sendersTo(tail) : msgQs[<<s, tail>>] /= << >>}) {
                sender_t := temp;
            };
            
            incomingReq_t:
            rcv(<<sender_t, tail>>, op_t); 
            totalOrder[op_t.obj] := Append(@, op_t);
            if (op_t.action = READ) {
                replyToReadReq_t: 
                resp_t := read(allObjLogs[tail], op_t.obj); 
                send(<<tail, sender_t>>, resp_t);        
            } else {
                allObjLogs[tail][op_t.obj] := Append(@, [uniqueId |-> op_t.uniqueId, isDirty |-> FALSE]);
                                 
                sendAck_t: send(<<tail, sender_t>>, [    obj |-> op_t.obj,
                                                            uniqueId |-> op_t.uniqueId,
                                                            action |-> WRITE]);     
            }; 
        }
    }
    
    fair process (n \in Nodes \ {head, tail})
        variables   prev = Predecessors[self],
                    succ = Successors[self],
                    op = defaultOp, resp = defaultOp, sender = defaultSrcDestNode; 
    {
        listen: while (TRUE) {
            
            
            with (temp \in {n \in sendersTo(self) : msgQs[<<n, self>>] /= << >>}) {
                sender := temp;
            };
            
            incomingReq:
            rcv(<<sender, self>>, op); 
            if (op.action = READ) {
            
                if (isDirtyVersion(allObjLogs[self], op.obj)) {
                    call query(self, tail, op, resp);
                } else {    
                    resp := read(allObjLogs[self], op.obj);
                };
                
                replyToReadReq: send(<<self, sender>>, resp);
            } else {
                dirtyWriteObj(allObjLogs[self], op.obj, op.uniqueId);
                    
                propagate: send(<<self, succ>>, op);
                    
                recvAck: rcv(<<succ, self>>, resp);
                    
                sendAck: applyDirtyWrite(allObjLogs[self], op.obj);
                send(<<self, prev>>, [  obj |-> op.obj,
                                                uniqueId |-> op.uniqueId,
                                                action |-> WRITE]); 
            }
        }  
    }
}
****************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "d09b5fa9" /\ chksum(tla) = "cf6b4f99")
VARIABLES msgQs, allObjLogs, clientOpSet, totalOrder, pc, stack

(* define statement *)
sendersTo(n) == IF n = head THEN Clients ELSE {Predecessors[n]} \cup Clients

read(objLogs, obj) == LET log == objLogs[obj] IN
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
          op_c, succ_h, op_h, resp_h, sender_h, op_t, resp_t, sender_t, prev, 
          succ, op, resp, sender

vars == << msgQs, allObjLogs, clientOpSet, totalOrder, pc, stack, src, dest, 
           op_query, resp_query, sequencer, objects, obj, resp_c, op_c, 
           succ_h, op_h, resp_h, sender_h, op_t, resp_t, sender_t, prev, succ, 
           op, resp, sender >>

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
        /\ sender_h = defaultClient
        (* Process tailProcess *)
        /\ op_t = defaultOp
        /\ resp_t = defaultOp
        /\ sender_t = defaultSrcDestNode
        (* Process n *)
        /\ prev = [self \in Nodes \ {head, tail} |-> Predecessors[self]]
        /\ succ = [self \in Nodes \ {head, tail} |-> Successors[self]]
        /\ op = [self \in Nodes \ {head, tail} |-> defaultOp]
        /\ resp = [self \in Nodes \ {head, tail} |-> defaultOp]
        /\ sender = [self \in Nodes \ {head, tail} |-> defaultSrcDestNode]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "newWrites"
                                        [] self = "head" -> "listen_h"
                                        [] self = "tail" -> "listen_t"
                                        [] self \in Nodes \ {head, tail} -> "listen"]

sendQuery(self) == /\ pc[self] = "sendQuery"
                   /\ msgQs' = [msgQs EXCEPT ![(<<src[self], dest[self]>>)] = Append(@, op_query[self])]
                   /\ pc' = [pc EXCEPT ![self] = "rcvResp"]
                   /\ UNCHANGED << allObjLogs, clientOpSet, totalOrder, stack, 
                                   src, dest, op_query, resp_query, sequencer, 
                                   objects, obj, resp_c, op_c, succ_h, op_h, 
                                   resp_h, sender_h, op_t, resp_t, sender_t, 
                                   prev, succ, op, resp, sender >>

rcvResp(self) == /\ pc[self] = "rcvResp"
                 /\ msgQs[(<<dest[self], src[self]>>)] /= << >>
                 /\ resp_query' = [resp_query EXCEPT ![self] = Head(msgQs[(<<dest[self], src[self]>>)])]
                 /\ msgQs' = [msgQs EXCEPT ![(<<dest[self], src[self]>>)] = Tail(@)]
                 /\ pc' = [pc EXCEPT ![self] = "ret"]
                 /\ UNCHANGED << allObjLogs, clientOpSet, totalOrder, stack, 
                                 src, dest, op_query, sequencer, objects, obj, 
                                 resp_c, op_c, succ_h, op_h, resp_h, sender_h, 
                                 op_t, resp_t, sender_t, prev, succ, op, resp, 
                                 sender >>

ret(self) == /\ pc[self] = "ret"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ src' = [src EXCEPT ![self] = Head(stack[self]).src]
             /\ dest' = [dest EXCEPT ![self] = Head(stack[self]).dest]
             /\ op_query' = [op_query EXCEPT ![self] = Head(stack[self]).op_query]
             /\ resp_query' = [resp_query EXCEPT ![self] = Head(stack[self]).resp_query]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << msgQs, allObjLogs, clientOpSet, totalOrder, 
                             sequencer, objects, obj, resp_c, op_c, succ_h, 
                             op_h, resp_h, sender_h, op_t, resp_t, sender_t, 
                             prev, succ, op, resp, sender >>

query(self) == sendQuery(self) \/ rcvResp(self) \/ ret(self)

newWrites(self) == /\ pc[self] = "newWrites"
                   /\ IF sequencer[self] <= NumWrites
                         THEN /\ pc' = [pc EXCEPT ![self] = "newObj_w"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "newReads"]
                   /\ UNCHANGED << msgQs, allObjLogs, clientOpSet, totalOrder, 
                                   stack, src, dest, op_query, resp_query, 
                                   sequencer, objects, obj, resp_c, op_c, 
                                   succ_h, op_h, resp_h, sender_h, op_t, 
                                   resp_t, sender_t, prev, succ, op, resp, 
                                   sender >>

newObj_w(self) == /\ pc[self] = "newObj_w"
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
                                                                         pc        |->  "decrement_w",
                                                                         src       |->  src[self],
                                                                         dest      |->  dest[self],
                                                                         op_query  |->  op_query[self],
                                                                         resp_query |->  resp_query[self] ] >>
                                                                     \o stack[self]]
                             /\ pc' = [pc EXCEPT ![self] = "sendQuery"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "increment_w"]
                             /\ UNCHANGED << stack, src, dest, op_query, 
                                             resp_query, obj, op_c >>
                  /\ UNCHANGED << msgQs, allObjLogs, clientOpSet, totalOrder, 
                                  sequencer, objects, resp_c, succ_h, op_h, 
                                  resp_h, sender_h, op_t, resp_t, sender_t, 
                                  prev, succ, op, resp, sender >>

decrement_w(self) == /\ pc[self] = "decrement_w"
                     /\ objects' = [objects EXCEPT ![self] = @ \ {obj[self]}]
                     /\ pc' = [pc EXCEPT ![self] = "newObj_w"]
                     /\ UNCHANGED << msgQs, allObjLogs, clientOpSet, 
                                     totalOrder, stack, src, dest, op_query, 
                                     resp_query, sequencer, obj, resp_c, op_c, 
                                     succ_h, op_h, resp_h, sender_h, op_t, 
                                     resp_t, sender_t, prev, succ, op, resp, 
                                     sender >>

increment_w(self) == /\ pc[self] = "increment_w"
                     /\ sequencer' = [sequencer EXCEPT ![self] = @ + 1]
                     /\ clientOpSet' = (clientOpSet \cup {op_c[self]})
                     /\ objects' = [objects EXCEPT ![self] = Objects]
                     /\ pc' = [pc EXCEPT ![self] = "newWrites"]
                     /\ UNCHANGED << msgQs, allObjLogs, totalOrder, stack, src, 
                                     dest, op_query, resp_query, obj, resp_c, 
                                     op_c, succ_h, op_h, resp_h, sender_h, 
                                     op_t, resp_t, sender_t, prev, succ, op, 
                                     resp, sender >>

newReads(self) == /\ pc[self] = "newReads"
                  /\ IF sequencer[self] <= NumWrites + NumReads
                        THEN /\ pc' = [pc EXCEPT ![self] = "newObj_r"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << msgQs, allObjLogs, clientOpSet, totalOrder, 
                                  stack, src, dest, op_query, resp_query, 
                                  sequencer, objects, obj, resp_c, op_c, 
                                  succ_h, op_h, resp_h, sender_h, op_t, resp_t, 
                                  sender_t, prev, succ, op, resp, sender >>

newObj_r(self) == /\ pc[self] = "newObj_r"
                  /\ IF objects[self] /= {}
                        THEN /\ obj' = [obj EXCEPT ![self] = CHOOSE o \in objects[self] : TRUE]
                             /\ op_c' = [op_c EXCEPT ![self] = [   obj |-> obj'[self],
                                                                   uniqueId |-> <<self, sequencer[self]>>,
                                                                   action |-> READ]]
                             /\ /\ dest' = [dest EXCEPT ![self] = head]
                                /\ op_query' = [op_query EXCEPT ![self] = op_c'[self]]
                                /\ resp_query' = [resp_query EXCEPT ![self] = resp_c[self]]
                                /\ src' = [src EXCEPT ![self] = self]
                                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "query",
                                                                         pc        |->  "decrement_r",
                                                                         src       |->  src[self],
                                                                         dest      |->  dest[self],
                                                                         op_query  |->  op_query[self],
                                                                         resp_query |->  resp_query[self] ] >>
                                                                     \o stack[self]]
                             /\ pc' = [pc EXCEPT ![self] = "sendQuery"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "increment_r"]
                             /\ UNCHANGED << stack, src, dest, op_query, 
                                             resp_query, obj, op_c >>
                  /\ UNCHANGED << msgQs, allObjLogs, clientOpSet, totalOrder, 
                                  sequencer, objects, resp_c, succ_h, op_h, 
                                  resp_h, sender_h, op_t, resp_t, sender_t, 
                                  prev, succ, op, resp, sender >>

decrement_r(self) == /\ pc[self] = "decrement_r"
                     /\ objects' = [objects EXCEPT ![self] = @ \ {obj[self]}]
                     /\ pc' = [pc EXCEPT ![self] = "newObj_r"]
                     /\ UNCHANGED << msgQs, allObjLogs, clientOpSet, 
                                     totalOrder, stack, src, dest, op_query, 
                                     resp_query, sequencer, obj, resp_c, op_c, 
                                     succ_h, op_h, resp_h, sender_h, op_t, 
                                     resp_t, sender_t, prev, succ, op, resp, 
                                     sender >>

increment_r(self) == /\ pc[self] = "increment_r"
                     /\ sequencer' = [sequencer EXCEPT ![self] = @ + 1]
                     /\ clientOpSet' = (clientOpSet \cup {op_c[self]})
                     /\ objects' = [objects EXCEPT ![self] = Objects]
                     /\ pc' = [pc EXCEPT ![self] = "newReads"]
                     /\ UNCHANGED << msgQs, allObjLogs, totalOrder, stack, src, 
                                     dest, op_query, resp_query, obj, resp_c, 
                                     op_c, succ_h, op_h, resp_h, sender_h, 
                                     op_t, resp_t, sender_t, prev, succ, op, 
                                     resp, sender >>

client(self) == newWrites(self) \/ newObj_w(self) \/ decrement_w(self)
                   \/ increment_w(self) \/ newReads(self) \/ newObj_r(self)
                   \/ decrement_r(self) \/ increment_r(self)

listen_h == /\ pc["head"] = "listen_h"
            /\ \E temp \in {s \in sendersTo(head): msgQs[<<s, head>>] /= << >>}:
                 sender_h' = temp
            /\ pc' = [pc EXCEPT !["head"] = "incomingReq_h"]
            /\ UNCHANGED << msgQs, allObjLogs, clientOpSet, totalOrder, stack, 
                            src, dest, op_query, resp_query, sequencer, 
                            objects, obj, resp_c, op_c, succ_h, op_h, resp_h, 
                            op_t, resp_t, sender_t, prev, succ, op, resp, 
                            sender >>

incomingReq_h == /\ pc["head"] = "incomingReq_h"
                 /\ msgQs[(<<sender_h, head>>)] /= << >>
                 /\ op_h' = Head(msgQs[(<<sender_h, head>>)])
                 /\ msgQs' = [msgQs EXCEPT ![(<<sender_h, head>>)] = Tail(@)]
                 /\ IF op_h'.action = READ
                       THEN /\ pc' = [pc EXCEPT !["head"] = "checkDirty_h"]
                            /\ UNCHANGED allObjLogs
                       ELSE /\ allObjLogs' = [allObjLogs EXCEPT ![head][(op_h'.obj)] = Append(@, [uniqueId |-> (op_h'.uniqueId), isDirty |-> TRUE])]
                            /\ pc' = [pc EXCEPT !["head"] = "propagate_h"]
                 /\ UNCHANGED << clientOpSet, totalOrder, stack, src, dest, 
                                 op_query, resp_query, sequencer, objects, obj, 
                                 resp_c, op_c, succ_h, resp_h, sender_h, op_t, 
                                 resp_t, sender_t, prev, succ, op, resp, 
                                 sender >>

checkDirty_h == /\ pc["head"] = "checkDirty_h"
                /\ IF isDirtyVersion(allObjLogs[head], op_h.obj)
                      THEN /\ pc' = [pc EXCEPT !["head"] = "apportion_h"]
                      ELSE /\ pc' = [pc EXCEPT !["head"] = "readFromSelf_h"]
                /\ UNCHANGED << msgQs, allObjLogs, clientOpSet, totalOrder, 
                                stack, src, dest, op_query, resp_query, 
                                sequencer, objects, obj, resp_c, op_c, succ_h, 
                                op_h, resp_h, sender_h, op_t, resp_t, sender_t, 
                                prev, succ, op, resp, sender >>

apportion_h == /\ pc["head"] = "apportion_h"
               /\ /\ dest' = [dest EXCEPT !["head"] = tail]
                  /\ op_query' = [op_query EXCEPT !["head"] = op_h]
                  /\ resp_query' = [resp_query EXCEPT !["head"] = resp_h]
                  /\ src' = [src EXCEPT !["head"] = head]
                  /\ stack' = [stack EXCEPT !["head"] = << [ procedure |->  "query",
                                                             pc        |->  "replyToReadReq_h",
                                                             src       |->  src["head"],
                                                             dest      |->  dest["head"],
                                                             op_query  |->  op_query["head"],
                                                             resp_query |->  resp_query["head"] ] >>
                                                         \o stack["head"]]
               /\ pc' = [pc EXCEPT !["head"] = "sendQuery"]
               /\ UNCHANGED << msgQs, allObjLogs, clientOpSet, totalOrder, 
                               sequencer, objects, obj, resp_c, op_c, succ_h, 
                               op_h, resp_h, sender_h, op_t, resp_t, sender_t, 
                               prev, succ, op, resp, sender >>

readFromSelf_h == /\ pc["head"] = "readFromSelf_h"
                  /\ resp_h' = read(allObjLogs[head], op_h.obj)
                  /\ pc' = [pc EXCEPT !["head"] = "replyToReadReq_h"]
                  /\ UNCHANGED << msgQs, allObjLogs, clientOpSet, totalOrder, 
                                  stack, src, dest, op_query, resp_query, 
                                  sequencer, objects, obj, resp_c, op_c, 
                                  succ_h, op_h, sender_h, op_t, resp_t, 
                                  sender_t, prev, succ, op, resp, sender >>

replyToReadReq_h == /\ pc["head"] = "replyToReadReq_h"
                    /\ msgQs' = [msgQs EXCEPT ![(<<head, sender_h>>)] = Append(@, resp_h)]
                    /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
                    /\ UNCHANGED << allObjLogs, clientOpSet, totalOrder, stack, 
                                    src, dest, op_query, resp_query, sequencer, 
                                    objects, obj, resp_c, op_c, succ_h, op_h, 
                                    resp_h, sender_h, op_t, resp_t, sender_t, 
                                    prev, succ, op, resp, sender >>

propagate_h == /\ pc["head"] = "propagate_h"
               /\ msgQs' = [msgQs EXCEPT ![(<<head, succ_h>>)] = Append(@, op_h)]
               /\ pc' = [pc EXCEPT !["head"] = "recvAck_h"]
               /\ UNCHANGED << allObjLogs, clientOpSet, totalOrder, stack, src, 
                               dest, op_query, resp_query, sequencer, objects, 
                               obj, resp_c, op_c, succ_h, op_h, resp_h, 
                               sender_h, op_t, resp_t, sender_t, prev, succ, 
                               op, resp, sender >>

recvAck_h == /\ pc["head"] = "recvAck_h"
             /\ msgQs[(<<succ_h, head>>)] /= << >>
             /\ resp_h' = Head(msgQs[(<<succ_h, head>>)])
             /\ msgQs' = [msgQs EXCEPT ![(<<succ_h, head>>)] = Tail(@)]
             /\ allObjLogs' = [allObjLogs EXCEPT ![head][(op_h.obj)] = Append(Tail(@), [Head(@) EXCEPT !.isDirty = FALSE])]
             /\ pc' = [pc EXCEPT !["head"] = "sendAck_h"]
             /\ UNCHANGED << clientOpSet, totalOrder, stack, src, dest, 
                             op_query, resp_query, sequencer, objects, obj, 
                             resp_c, op_c, succ_h, op_h, sender_h, op_t, 
                             resp_t, sender_t, prev, succ, op, resp, sender >>

sendAck_h == /\ pc["head"] = "sendAck_h"
             /\ msgQs' = [msgQs EXCEPT ![(<<head, sender_h>>)] = Append(@, ([   obj |-> op_h.obj,
                                                                                uniqueId |-> op_h.uniqueId,
                                                                                action |-> WRITE]))]
             /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
             /\ UNCHANGED << allObjLogs, clientOpSet, totalOrder, stack, src, 
                             dest, op_query, resp_query, sequencer, objects, 
                             obj, resp_c, op_c, succ_h, op_h, resp_h, sender_h, 
                             op_t, resp_t, sender_t, prev, succ, op, resp, 
                             sender >>

headProcess == listen_h \/ incomingReq_h \/ checkDirty_h \/ apportion_h
                  \/ readFromSelf_h \/ replyToReadReq_h \/ propagate_h
                  \/ recvAck_h \/ sendAck_h

listen_t == /\ pc["tail"] = "listen_t"
            /\ \E temp \in {s \in sendersTo(tail) : msgQs[<<s, tail>>] /= << >>}:
                 sender_t' = temp
            /\ pc' = [pc EXCEPT !["tail"] = "incomingReq_t"]
            /\ UNCHANGED << msgQs, allObjLogs, clientOpSet, totalOrder, stack, 
                            src, dest, op_query, resp_query, sequencer, 
                            objects, obj, resp_c, op_c, succ_h, op_h, resp_h, 
                            sender_h, op_t, resp_t, prev, succ, op, resp, 
                            sender >>

incomingReq_t == /\ pc["tail"] = "incomingReq_t"
                 /\ msgQs[(<<sender_t, tail>>)] /= << >>
                 /\ op_t' = Head(msgQs[(<<sender_t, tail>>)])
                 /\ msgQs' = [msgQs EXCEPT ![(<<sender_t, tail>>)] = Tail(@)]
                 /\ totalOrder' = [totalOrder EXCEPT ![op_t'.obj] = Append(@, op_t')]
                 /\ IF op_t'.action = READ
                       THEN /\ pc' = [pc EXCEPT !["tail"] = "replyToReadReq_t"]
                            /\ UNCHANGED allObjLogs
                       ELSE /\ allObjLogs' = [allObjLogs EXCEPT ![tail][op_t'.obj] = Append(@, [uniqueId |-> op_t'.uniqueId, isDirty |-> FALSE])]
                            /\ pc' = [pc EXCEPT !["tail"] = "sendAck_t"]
                 /\ UNCHANGED << clientOpSet, stack, src, dest, op_query, 
                                 resp_query, sequencer, objects, obj, resp_c, 
                                 op_c, succ_h, op_h, resp_h, sender_h, resp_t, 
                                 sender_t, prev, succ, op, resp, sender >>

replyToReadReq_t == /\ pc["tail"] = "replyToReadReq_t"
                    /\ resp_t' = read(allObjLogs[tail], op_t.obj)
                    /\ msgQs' = [msgQs EXCEPT ![(<<tail, sender_t>>)] = Append(@, resp_t')]
                    /\ pc' = [pc EXCEPT !["tail"] = "listen_t"]
                    /\ UNCHANGED << allObjLogs, clientOpSet, totalOrder, stack, 
                                    src, dest, op_query, resp_query, sequencer, 
                                    objects, obj, resp_c, op_c, succ_h, op_h, 
                                    resp_h, sender_h, op_t, sender_t, prev, 
                                    succ, op, resp, sender >>

sendAck_t == /\ pc["tail"] = "sendAck_t"
             /\ msgQs' = [msgQs EXCEPT ![(<<tail, sender_t>>)] = Append(@, ([    obj |-> op_t.obj,
                                                                                    uniqueId |-> op_t.uniqueId,
                                                                                    action |-> WRITE]))]
             /\ pc' = [pc EXCEPT !["tail"] = "listen_t"]
             /\ UNCHANGED << allObjLogs, clientOpSet, totalOrder, stack, src, 
                             dest, op_query, resp_query, sequencer, objects, 
                             obj, resp_c, op_c, succ_h, op_h, resp_h, sender_h, 
                             op_t, resp_t, sender_t, prev, succ, op, resp, 
                             sender >>

tailProcess == listen_t \/ incomingReq_t \/ replyToReadReq_t \/ sendAck_t

listen(self) == /\ pc[self] = "listen"
                /\ \E temp \in {n \in sendersTo(self) : msgQs[<<n, self>>] /= << >>}:
                     sender' = [sender EXCEPT ![self] = temp]
                /\ pc' = [pc EXCEPT ![self] = "incomingReq"]
                /\ UNCHANGED << msgQs, allObjLogs, clientOpSet, totalOrder, 
                                stack, src, dest, op_query, resp_query, 
                                sequencer, objects, obj, resp_c, op_c, succ_h, 
                                op_h, resp_h, sender_h, op_t, resp_t, sender_t, 
                                prev, succ, op, resp >>

incomingReq(self) == /\ pc[self] = "incomingReq"
                     /\ msgQs[(<<sender[self], self>>)] /= << >>
                     /\ op' = [op EXCEPT ![self] = Head(msgQs[(<<sender[self], self>>)])]
                     /\ msgQs' = [msgQs EXCEPT ![(<<sender[self], self>>)] = Tail(@)]
                     /\ IF op'[self].action = READ
                           THEN /\ IF isDirtyVersion(allObjLogs[self], op'[self].obj)
                                      THEN /\ /\ dest' = [dest EXCEPT ![self] = tail]
                                              /\ op_query' = [op_query EXCEPT ![self] = op'[self]]
                                              /\ resp_query' = [resp_query EXCEPT ![self] = resp[self]]
                                              /\ src' = [src EXCEPT ![self] = self]
                                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "query",
                                                                                       pc        |->  "replyToReadReq",
                                                                                       src       |->  src[self],
                                                                                       dest      |->  dest[self],
                                                                                       op_query  |->  op_query[self],
                                                                                       resp_query |->  resp_query[self] ] >>
                                                                                   \o stack[self]]
                                           /\ pc' = [pc EXCEPT ![self] = "sendQuery"]
                                           /\ resp' = resp
                                      ELSE /\ resp' = [resp EXCEPT ![self] = read(allObjLogs[self], op'[self].obj)]
                                           /\ pc' = [pc EXCEPT ![self] = "replyToReadReq"]
                                           /\ UNCHANGED << stack, src, dest, 
                                                           op_query, 
                                                           resp_query >>
                                /\ UNCHANGED allObjLogs
                           ELSE /\ allObjLogs' = [allObjLogs EXCEPT ![self][(op'[self].obj)] = Append(@, [uniqueId |-> (op'[self].uniqueId), isDirty |-> TRUE])]
                                /\ pc' = [pc EXCEPT ![self] = "propagate"]
                                /\ UNCHANGED << stack, src, dest, op_query, 
                                                resp_query, resp >>
                     /\ UNCHANGED << clientOpSet, totalOrder, sequencer, 
                                     objects, obj, resp_c, op_c, succ_h, op_h, 
                                     resp_h, sender_h, op_t, resp_t, sender_t, 
                                     prev, succ, sender >>

replyToReadReq(self) == /\ pc[self] = "replyToReadReq"
                        /\ msgQs' = [msgQs EXCEPT ![(<<self, sender[self]>>)] = Append(@, resp[self])]
                        /\ pc' = [pc EXCEPT ![self] = "listen"]
                        /\ UNCHANGED << allObjLogs, clientOpSet, totalOrder, 
                                        stack, src, dest, op_query, resp_query, 
                                        sequencer, objects, obj, resp_c, op_c, 
                                        succ_h, op_h, resp_h, sender_h, op_t, 
                                        resp_t, sender_t, prev, succ, op, resp, 
                                        sender >>

propagate(self) == /\ pc[self] = "propagate"
                   /\ msgQs' = [msgQs EXCEPT ![(<<self, succ[self]>>)] = Append(@, op[self])]
                   /\ pc' = [pc EXCEPT ![self] = "recvAck"]
                   /\ UNCHANGED << allObjLogs, clientOpSet, totalOrder, stack, 
                                   src, dest, op_query, resp_query, sequencer, 
                                   objects, obj, resp_c, op_c, succ_h, op_h, 
                                   resp_h, sender_h, op_t, resp_t, sender_t, 
                                   prev, succ, op, resp, sender >>

recvAck(self) == /\ pc[self] = "recvAck"
                 /\ msgQs[(<<succ[self], self>>)] /= << >>
                 /\ resp' = [resp EXCEPT ![self] = Head(msgQs[(<<succ[self], self>>)])]
                 /\ msgQs' = [msgQs EXCEPT ![(<<succ[self], self>>)] = Tail(@)]
                 /\ pc' = [pc EXCEPT ![self] = "sendAck"]
                 /\ UNCHANGED << allObjLogs, clientOpSet, totalOrder, stack, 
                                 src, dest, op_query, resp_query, sequencer, 
                                 objects, obj, resp_c, op_c, succ_h, op_h, 
                                 resp_h, sender_h, op_t, resp_t, sender_t, 
                                 prev, succ, op, sender >>

sendAck(self) == /\ pc[self] = "sendAck"
                 /\ allObjLogs' = [allObjLogs EXCEPT ![self][(op[self].obj)] = Append(Tail(@), [Head(@) EXCEPT !.isDirty = FALSE])]
                 /\ msgQs' = [msgQs EXCEPT ![(<<self, prev[self]>>)] = Append(@, ([  obj |-> op[self].obj,
                                                                                             uniqueId |-> op[self].uniqueId,
                                                                                             action |-> WRITE]))]
                 /\ pc' = [pc EXCEPT ![self] = "listen"]
                 /\ UNCHANGED << clientOpSet, totalOrder, stack, src, dest, 
                                 op_query, resp_query, sequencer, objects, obj, 
                                 resp_c, op_c, succ_h, op_h, resp_h, sender_h, 
                                 op_t, resp_t, sender_t, prev, succ, op, resp, 
                                 sender >>

n(self) == listen(self) \/ incomingReq(self) \/ replyToReadReq(self)
              \/ propagate(self) \/ recvAck(self) \/ sendAck(self)

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
                    /\ sender_h     \in Clients
                    /\ succ         \in [Nodes \ {head, tail} -> Nodes \ {head}]
                    /\ prev         \in [Nodes \ {head, tail} -> Nodes \ {tail}]
                    /\ op           \in [Nodes \ {head, tail} -> OperationType]
                    /\ resp         \in [Nodes \ {head, tail} -> OperationType]
                    /\ sender       \in [Nodes \ {head, tail} -> Clients \cup (Nodes \ {tail})]   
                    /\ resp_t       \in OperationType
                    /\ op_t         \in OperationType
                    /\ sender_t     \in Clients \cup (Nodes \ {tail})
                    

RECURSIVE clean(_)
clean(log) == IF log = << >> \/ ~Head(log).isDirty THEN log ELSE clean(Tail(log))

Terminated == \A o \in Objects : LET headLog == allObjLogs[head][o]
                                    IN  /\ headLog = clean(headLog) 
                                        /\ Len(headLog) = NumMsgs
                                    
PostCondition == \A node \in Nodes \ {tail}: \A o \in Objects : 
                    LET log == allObjLogs[node][o]
                        tailLog == allObjLogs[tail][o] IN log = tailLog

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
\* Last modified Thu Jun 15 14:36:53 EDT 2023 by jenniferlam
\* Last modified Fri Jun 02 18:58:13 EDT 2023 by 72jen
\* Created Thu May 25 11:58:00 EDT 2023 by jenniferlam
