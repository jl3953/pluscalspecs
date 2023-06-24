----------------------------- MODULE CRAQRetry -----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Clients, Nodes, head, tail, NumWrites, NumReads, Objects, MaxTimestamp

NumMsgs == 10

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
NullUniqueId == CHOOSE id : id \notin UniqueIdType
SendersTo(n) == {edge[1]: edge \in {e \in Network: e[2] = n}}

ASSUME  /\ head \in Nodes
        /\ tail \in Nodes
        /\ Cardinality(Nodes) >= 2
        /\ Cardinality(Edges) = Cardinality(Nodes \ {head}) * 2 + Cardinality(Nodes \ {tail}) * 2 - 2
        /\ Edges \subseteq Network
        /\ ClientEdges \subseteq Network
\*        /\ Cardinality(UniqueIdType) = Cardinality(Clients) * (NumMsgs + 1)
        
-----------------------------------------------------------------------------
\* CallType
READ_INV == "READ_INV" \* Read invocation
WRITE_INV == "WRITE_INV" \* Write invocation
READ_RESP == "READ_RESP" \* Read response
WRITE_RESP == "WRITE_RESP" \* Write response

\* CommitType
CLEAN == "CLEAN"
DIRTY == "DIRTY"


NullNode == CHOOSE n : n \notin Nodes
\*NullObj == CHOOSE o : o \notin Objects
\*NullClient == CHOOSE c : c \notin Clients
NullObj == CHOOSE o \in Objects: TRUE
NullClient == CHOOSE c \in Clients: TRUE


CallType == {READ_INV, WRITE_INV, READ_RESP, WRITE_RESP}
NullCall == CHOOSE call \in CallType: TRUE

CommitType == {CLEAN, DIRTY}
NullCommitStatus == CHOOSE status : status \notin CommitType

TimestampType == { t: t \in 0..MaxTimestamp}
NullTs == CHOOSE ts : ts \notin TimestampType
ObjectVersionType == [  obj: Objects, 
                        uniqueId: UniqueIdType \cup {NullUniqueId}, 
                        writeStartTs: TimestampType \cup {NullTs}, 
                        writeCommitTs: TimestampType \cup {NullTs}, 
                        commitStatus: CommitType \cup {NullCommitStatus}]
             
RequestType == [callType: CallType, 
                uniqueId: UniqueIdType \cup {NullUniqueId},
                startTs: TimestampType \cup {NullTs},
                commitTs: TimestampType \cup {NullTs},
                op: ObjectVersionType]
NullReq == CHOOSE r : r \notin RequestType

Cons(item, seq) == << item >> \o seq   

PendingInvoType == { <<id, node>>: id \in UniqueIdType, node \in Nodes} 
               

(****************************************************************************
--fair algorithm CRAQRetry {

    \* declaration of global algorithms
    variables   msgQs = [edge \in Network |-> << >>], \* in-order delivery via TCP
                objLogs = [n \in Nodes |-> [o \in Objects |-> << >>]],
                objTotalOrders = [ o \in Objects |-> << >> ],
                allSubmittedWriteOps = [o \in Objects |-> {}],
                allSubmittedReadOps = [ o \in Objects |-> {}],
                terminatedYet = [c \in Clients |-> FALSE],
                initClient = CHOOSE c \in Clients: TRUE,
                nonInitClients = Clients \ {initClient},
                start = FALSE,
                timeOracle = 10,
                isLinearizable = TRUE;
                
    \* operator definitions
    define {
        
        RECURSIVE CommitDirtyVersion(_, _) 
        CommitDirtyVersion(objLog, committedVer) == LET mostRecentVer == Head(objLog)
                                                        uniqueId == committedVer.uniqueId
                                                        writeCommitTs == committedVer.writeCommitTs IN 
                                                    IF mostRecentVer.uniqueId = uniqueId THEN
                                                        Cons([mostRecentVer EXCEPT !.commitStatus = CLEAN,
                                                                                    !.writeCommitTs = writeCommitTs], 
                                                                Tail(objLog))
                                                    ELSE
                                                        Cons(mostRecentVer, 
                                                                CommitDirtyVersion(Tail(objLog), committedVer))
        
        IsDirty(node, obj) == Head(objLogs[node][obj]).commitStatus = DIRTY        
        Read(node, obj) == Head(objLogs[node][obj])
        FindPair(set, k) == CHOOSE kv \in set: kv[1] = k
        Find(set, k) == LET kv == FindPair(set, k) IN kv[2]
        
        Increment(id) == <<id[1], id[2]+1>>
        
    }
    
    \* macro definitions
    macro send(sender, receiver, msg) {
        msgQs[<<sender, receiver>>] := Append(@, msg)
    }
    
    macro recv(sender, receiver, msg) {
        msg := Head(msgQs[<<sender, receiver>>]);
        msgQs[<<sender, receiver>>] := Tail(@);
    }
    
    macro add(set, k, v) {
        set := set \cup {<<k, v>>};
    }
    
    macro remove(set, k) {
        set := set \ {FindPair(set, k)};
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
    
    macro addToOpSet(reqOp) {
        if (reqOp.callType = WRITE_RESP) {
            allSubmittedWriteOps[reqOp.op.obj] := allSubmittedWriteOps[reqOp.op.obj] \cup {reqOp};
        } else {
            allSubmittedReadOps[reqOp.op.obj] := allSubmittedReadOps[reqOp.op.obj] \cup {reqOp};
        }
    }

    fair process(iclient = "initClient")
        variables   uninitializedObjs = Objects,
                    initObj = NullObj,
                    objs_init = Objects,
                    obj_init = NullObj,
                    actions_init = {WRITE_INV, READ_INV},
                    action_init = NullCall,
                    gateway_cinit = NullNode,
                    msg_cinit = NullReq,
                    uniqueId_cinit = <<initClient, 1>>,
                    sentOps_init = 0,
                    recvdOps_init = 0;
    {
        initializeObj: while (uninitializedObjs /= {}) {
            initObj := CHOOSE o \in uninitializedObjs: TRUE;
            send(initClient, head, [callType |-> WRITE_INV,
                                    uniqueId |-> uniqueId_cinit,
                                    startTs |-> NullTs,
                                    commitTs |-> NullTs,
                                    op |-> [obj |-> initObj,
                                            uniqueId |-> uniqueId_cinit,
                                            writeStartTs |-> NullTs,
                                            writeCommitTs |-> NullTs,
                                            commitStatus |-> DIRTY]]);
            
            uninitializedObjs := uninitializedObjs \ {initObj};
            uniqueId_cinit := Increment(uniqueId_cinit);
            
            waitForInit:
            when msgQs[<<head, initClient>>] /= << >>; 
            recv(head, initClient, msg_cinit); 
            addToOpSet(msg_cinit);
        };
        start := TRUE;
        
        concurrentOps_init: while (objs_init /= {}) {
            obj_init := CHOOSE o \in objs_init: TRUE;
            objs_init := objs_init \ {obj_init};
            actions_init := {WRITE_INV, READ_INV};
            
            readOrWrite_init: while (actions_init /= {}) {
                action_init := CHOOSE a \in actions_init: TRUE;
                actions_init := actions_init \ {action_init};
                
                send(initClient, head, [callType |-> action_init,
                                        uniqueId |-> uniqueId_cinit,
                                        startTs |-> NullTs,
                                        commitTs |-> NullTs,
                                        op |-> [obj |-> obj_init,
                                                uniqueId |-> uniqueId_cinit,
                                                writeStartTs |-> NullTs,
                                                writeCommitTs |-> NullTs,
                                                commitStatus |-> IF action_init = WRITE_INV 
                                                                    THEN DIRTY 
                                                                    ELSE NullCommitStatus]]);
                uniqueId_cinit := Increment(uniqueId_cinit);
                sentOps_init := sentOps_init + 1;
            };

        };
        
        waitForOps_init:
        while (recvdOps_init < sentOps_init) {
            block_init: with (temp \in {s \in SendersTo(initClient): msgQs[<<s, initClient>>] /= << >>}) {
                gateway_cinit := temp;
            };
            moreblock_init: when msgQs[<<gateway_cinit, initClient>>] /= << >>; 
            recv_init: recv(gateway_cinit, initClient, msg_cinit);
            add_init: addToOpSet(msg_cinit); 
            increment_init: recvdOps_init := recvdOps_init + 1;
        };
        
\*        wait1: with (temp \in {s \in SendersTo(initClient): msgQs[<<s, initClient>>] /= << >>}) {
\*            gateway_cinit := temp;
\*        };
\*        when msgQs[<<gateway_cinit, initClient>>] /= << >>;
\*        recv(gateway_cinit, initClient, msg_cinit);
\*        addToOpSet(msg_cinit);
\*        increment1: recvdOps_init := recvdOps_init + 1;
\*        
\*        wait2: with (temp \in {s \in SendersTo(initClient): msgQs[<<s, initClient>>] /= << >>}) {
\*            gateway_cinit := temp;
\*        };
\*        when msgQs[<<gateway_cinit, initClient>>] /= << >>;
\*        recv(gateway_cinit, initClient, msg_cinit);
\*        addToOpSet(msg_cinit);
\*        increment2: recvdOps_init := recvdOps_init + 1;
\*        
\*        wait3: with (temp \in {s \in SendersTo(initClient): msgQs[<<s, initClient>>] /= << >>}) {
\*            gateway_cinit := temp;
\*        };
\*        when msgQs[<<gateway_cinit, initClient>>] /= << >>;
\*        recv(gateway_cinit, initClient, msg_cinit);
\*        addToOpSet(msg_cinit);
\*        increment3: recvdOps_init := recvdOps_init + 1;
\*        
\*        wait4: with (temp \in {s \in SendersTo(initClient): msgQs[<<s, initClient>>] /= << >>}) {
\*            gateway_cinit := temp;
\*        };
\*        when msgQs[<<gateway_cinit, initClient>>] /= << >>;
\*        recv(gateway_cinit, initClient, msg_cinit);
\*        addToOpSet(msg_cinit);
\*        increment4: recvdOps_init := recvdOps_init + 1;
        
        terminate_init: terminatedYet[initClient] := TRUE
    }
    
    fair process(c \in nonInitClients)
        variables   objs = Objects,
                    obj = NullObj,
                    actions = {WRITE_INV, READ_INV},
                    action = NullCall,
                    gateway_c = NullNode,
                    msg_c = NullReq,
                    uniqueId = <<self, 1>>,
                    sentOps = 0,
                    recvdOps = 0;
    {   
        waitForInit: when start = TRUE;
        concurrentOps: 
        while (objs /= {}) {
            obj := CHOOSE o \in objs: TRUE;
            objs := objs \ {obj};
            
            readOrWrite: 
            while (actions /= {}) {
                action := CHOOSE a \in actions: TRUE;
                actions := actions \ {action};
                
                send(   self, 
                        IF action = WRITE_INV THEN head ELSE CHOOSE n \in Nodes: n /= head, 
                        [   callType |-> action,
                            uniqueId |-> uniqueId,
                            startTs |-> NullTs,
                            commitTs |-> NullTs,
                            op |-> [obj |-> obj,
                                    uniqueId |-> uniqueId,
                                    writeStartTs |-> NullTs,
                                    writeCommitTs |-> NullTs,
                                    commitStatus |-> IF action = WRITE_INV 
                                                        THEN DIRTY 
                                                        ELSE NullCommitStatus]]);
                uniqueId := Increment(uniqueId);
                sentOps := sentOps + 1;
            };
            actions := {WRITE_INV, READ_INV}; 
            
        };
        
        waitForOps:
        while (recvdOps < sentOps) {
            with (temp \in {s \in SendersTo(self): msgQs[<<s, self>>] /= << >>}) {
                gateway_c := temp;
            };
            when msgQs[<<gateway_c, self>>] /= << >>; 
            recv(gateway_c, self, msg_c); 
            addToOpSet(msg_c);
            assert(msg_c.uniqueId[1] = self);
            recvdOps := recvdOps + 1;
        };
        
        terminate: terminatedYet[self] := TRUE;
    }
   
    
    fair process(he="head") 
        variables req_h = NullReq,
                  sender_h = NullNode,
                  pendingInvos_h = {},
                  now_h = timeOracle;
    {
        listen_h: while (TRUE) {
            with (temp \in {s \in SendersTo(head): msgQs[<<s, head>>] /= << >>}) {
                sender_h := temp;
            }; 
            
            incomingMsg_h:
            when msgQs[<<sender_h, head>>] /= << >>;  
            recv(sender_h, head, req_h);
            
            if (req_h.callType = READ_INV) {
                if (IsDirty(head, req_h.op.obj)) {
                    apportionQ_h: send(head, tail, req_h);
                    add(pendingInvos_h, req_h.uniqueId, sender_h);
                } else {
                    now_h := timeOracle;
                    timeOracle := timeOracle + 1;
                    addReadTO_h: req_h := [ callType |-> READ_RESP,
                                            uniqueId |-> req_h.uniqueId,
                                            startTs |-> timeOracle,
                                            commitTs |-> timeOracle,
                                            op |-> Read(head, req_h.op.obj)];
                    objTotalOrders[req_h.op.obj] := Cons(req_h, @);
                    respFromHead: send(head, sender_h, req_h);
                }
            } else {
                if (req_h.callType = READ_RESP) {
                    readResp_h: send(head, Find(pendingInvos_h, req_h.uniqueId), req_h);
                    remove(pendingInvos_h, req_h.uniqueId);
                } else {
                    if (req_h.callType = WRITE_INV) {
                        now_h := timeOracle;
                        timeOracle := timeOracle + 1;
                        dirtyWrite_h: req_h := [req_h EXCEPT    !.startTs = now_h,
                                                                !.op.writeStartTs = now_h,
                                                                !.op.commitStatus = DIRTY];
                        write(head, req_h.op);
                        propagate_h: send(head, Successors[head], req_h);
                        add(pendingInvos_h, req_h.uniqueId, sender_h);
                    } else { \* WRITE_RESP
                        objLogs[head][req_h.op.obj] := CommitDirtyVersion(@, req_h.op);
                        respToClient: send(head, Find(pendingInvos_h, req_h.uniqueId), req_h);
                        remove(pendingInvos_h, req_h.uniqueId);
                    }
                }
            }
        }
    }
    
    fair process(ta="tail")
        variables   req_t = NullReq,
                    sender_t = NullNode,
                    pendingInvos_t = {},
                    now_t = timeOracle;
    {
        listen_t: while (TRUE) {
            with (temp \in {s \in SendersTo(tail) : msgQs[<<s, tail>>] /= << >>}) {
                sender_t := temp;
            };
            
            incomingMsg_t:
            when msgQs[<<sender_t, tail>>] /= << >>;  
            recv(sender_t, tail, req_t);
            if (req_t.callType = READ_INV) {
                now_t := timeOracle;
                timeOracle := timeOracle + 1;
                addReadTO_t: req_t := [ callType |-> READ_RESP,
                                        uniqueId |-> req_t.uniqueId,
                                        startTs |-> now_t,
                                        commitTs |-> now_t,
                                        op |-> Read(tail, req_t.op.obj)];
                objTotalOrders[req_t.op.obj] := Cons(req_t, @);
                respFromSelf_t: send(tail, sender_t, req_t);
            } else { \* WRITE_INV
                now_t := timeOracle;
                timeOracle := timeOracle + 1;
                write(tail, [req_t.op EXCEPT  !.writeCommitTs = now_t, 
                                              !.commitStatus = CLEAN]);
                addWriteTO_t: req_t := [    callType |-> WRITE_RESP,
                                            uniqueId |-> req_t.uniqueId,
                                            startTs |-> req_t.startTs,
                                            commitTs |-> Read(tail, req_t.op.obj).writeCommitTs,
                                            op |-> Read(tail, req_t.op.obj)];
                objTotalOrders[req_t.op.obj] := Cons(req_t, @);
                tailAck: send(tail, Predecessors[tail], req_t);   
            }
        }
    }
    
    fair process(n \in Nodes \ {head, tail})
        variables   req = NullReq,
                    sender = NullNode,
                    now = timeOracle, 
                    pendingInvos = {};
    {
        listen: while (TRUE) {
            with (temp \in {s \in SendersTo(self) : msgQs[<<s, self>>] /= << >>}) {
                sender := temp;
            };
            
            incomingMsg:
            when msgQs[<<sender, self>>] /= << >>;  
            recv(sender, self, req); 
            
            if (req.callType = READ_INV) {
                if (IsDirty(self, req.op.obj)) {                 
                    apportionQ: send(self, tail, req);
                    add(pendingInvos, req.uniqueId, sender);
                } else {
                    now := timeOracle;
                    timeOracle := timeOracle + 1;
                    addReadTO: req :=  [callType |-> READ_RESP,
                                        uniqueId |-> req.uniqueId,
                                        startTs |-> now,
                                        commitTs |-> now,
                                        op |-> Read(self, req.op.obj)];
                    objTotalOrders[req.op.obj] := Cons(req, @);
                    respFromSelf: send(self, sender, req);
                } 
            } else {
                if (req.callType = READ_RESP) {
                    fwdFromTail: send(self, Find(pendingInvos, req.uniqueId), req);
                    remove(pendingInvos, req.uniqueId);
                } else { 
                    if (req.callType = WRITE_INV) {
                        write(self, req.op);
                        
                        propagate: send(self, Successors[self], req);
                        add(pendingInvos, req.uniqueId, sender)
                    } else { \* WRITE_RESP
                        
                        objLogs[self][req.op.obj] := CommitDirtyVersion(@, req.op);
                        
                        backProp: send(self, Find(pendingInvos, req.uniqueId), req);
                        remove(pendingInvos, req.uniqueId);
                    };
                }
            }  
        }
    }
    
    fair process(perObj \in Objects)
        variables   submittedOps = {},
                    writes = {},
                    reads = {},
                    read = NullReq,
                    edges = {},
                    clients = Clients,
                    match = NullReq,
                    cli = NullClient;
    {
        \* runs at the end
        awaitTermination: while (clients /= {}) {
            cli := CHOOSE cl \in clients : TRUE;
            clients := clients \ {cli};
            await terminatedYet[cli] = TRUE;
        };
        
        writes := allSubmittedWriteOps[self];
        edges := {edge \in {<<w1, w2>> : w1, w2 \in writes}: edge[1].commitTs < edge[2].startTs};

        reads := allSubmittedReadOps[self];
        addVToG: while (reads /= {}) {
            read := CHOOSE r \in reads: TRUE;
            reads := reads \ {read};
            
            \* add_to_graph(read)
            edges := edges \cup {<<write, read>>: write \in {w \in writes: w.commitTs < read.startTs}}; 
            
            \* find_matched_write(read)
            match := CHOOSE w \in writes: w.uniqueId = read.op.uniqueId;
            
            \* merge_read_into_write(read, match)
            merge_read_into_write: 
            edges := edges \cup { <<write, match>>: write \in {w \in writes: w.commitTs < read.startTs}};
            removeSelfEdges: 
            edges := edges \ {e \in edges: e[1] = e[2]}; 
            
            \* check for cycles
            if (\E e \in edges: <<e[2], e[1]>> \in edges) {
                isLinearizable := FALSE
            }
            
        }
    }
}

****************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "aa9be7bb" /\ chksum(tla) = "832a7022")
\* Label waitForInit of process iclient at line 191 col 13 changed to waitForInit_
VARIABLES msgQs, objLogs, objTotalOrders, allSubmittedWriteOps, 
          allSubmittedReadOps, terminatedYet, initClient, nonInitClients, 
          start, timeOracle, isLinearizable, pc

(* define statement *)
RECURSIVE CommitDirtyVersion(_, _)
CommitDirtyVersion(objLog, committedVer) == LET mostRecentVer == Head(objLog)
                                                uniqueId == committedVer.uniqueId
                                                writeCommitTs == committedVer.writeCommitTs IN
                                            IF mostRecentVer.uniqueId = uniqueId THEN
                                                Cons([mostRecentVer EXCEPT !.commitStatus = CLEAN,
                                                                            !.writeCommitTs = writeCommitTs],
                                                        Tail(objLog))
                                            ELSE
                                                Cons(mostRecentVer,
                                                        CommitDirtyVersion(Tail(objLog), committedVer))

IsDirty(node, obj) == Head(objLogs[node][obj]).commitStatus = DIRTY
Read(node, obj) == Head(objLogs[node][obj])
FindPair(set, k) == CHOOSE kv \in set: kv[1] = k
Find(set, k) == LET kv == FindPair(set, k) IN kv[2]

Increment(id) == <<id[1], id[2]+1>>

VARIABLES uninitializedObjs, initObj, objs_init, obj_init, actions_init, 
          action_init, gateway_cinit, msg_cinit, uniqueId_cinit, sentOps_init, 
          recvdOps_init, objs, obj, actions, action, gateway_c, msg_c, 
          uniqueId, sentOps, recvdOps, req_h, sender_h, pendingInvos_h, now_h, 
          req_t, sender_t, pendingInvos_t, now_t, req, sender, now, 
          pendingInvos, submittedOps, writes, reads, read, edges, clients, 
          match, cli

vars == << msgQs, objLogs, objTotalOrders, allSubmittedWriteOps, 
           allSubmittedReadOps, terminatedYet, initClient, nonInitClients, 
           start, timeOracle, isLinearizable, pc, uninitializedObjs, initObj, 
           objs_init, obj_init, actions_init, action_init, gateway_cinit, 
           msg_cinit, uniqueId_cinit, sentOps_init, recvdOps_init, objs, obj, 
           actions, action, gateway_c, msg_c, uniqueId, sentOps, recvdOps, 
           req_h, sender_h, pendingInvos_h, now_h, req_t, sender_t, 
           pendingInvos_t, now_t, req, sender, now, pendingInvos, 
           submittedOps, writes, reads, read, edges, clients, match, cli >>

ProcSet == {"initClient"} \cup (nonInitClients) \cup {"head"} \cup {"tail"} \cup (Nodes \ {head, tail}) \cup (Objects)

Init == (* Global variables *)
        /\ msgQs = [edge \in Network |-> << >>]
        /\ objLogs = [n \in Nodes |-> [o \in Objects |-> << >>]]
        /\ objTotalOrders = [ o \in Objects |-> << >> ]
        /\ allSubmittedWriteOps = [o \in Objects |-> {}]
        /\ allSubmittedReadOps = [ o \in Objects |-> {}]
        /\ terminatedYet = [c \in Clients |-> FALSE]
        /\ initClient = (CHOOSE c \in Clients: TRUE)
        /\ nonInitClients = Clients \ {initClient}
        /\ start = FALSE
        /\ timeOracle = 10
        /\ isLinearizable = TRUE
        (* Process iclient *)
        /\ uninitializedObjs = Objects
        /\ initObj = NullObj
        /\ objs_init = Objects
        /\ obj_init = NullObj
        /\ actions_init = {WRITE_INV, READ_INV}
        /\ action_init = NullCall
        /\ gateway_cinit = NullNode
        /\ msg_cinit = NullReq
        /\ uniqueId_cinit = <<initClient, 1>>
        /\ sentOps_init = 0
        /\ recvdOps_init = 0
        (* Process c *)
        /\ objs = [self \in nonInitClients |-> Objects]
        /\ obj = [self \in nonInitClients |-> NullObj]
        /\ actions = [self \in nonInitClients |-> {WRITE_INV, READ_INV}]
        /\ action = [self \in nonInitClients |-> NullCall]
        /\ gateway_c = [self \in nonInitClients |-> NullNode]
        /\ msg_c = [self \in nonInitClients |-> NullReq]
        /\ uniqueId = [self \in nonInitClients |-> <<self, 1>>]
        /\ sentOps = [self \in nonInitClients |-> 0]
        /\ recvdOps = [self \in nonInitClients |-> 0]
        (* Process he *)
        /\ req_h = NullReq
        /\ sender_h = NullNode
        /\ pendingInvos_h = {}
        /\ now_h = timeOracle
        (* Process ta *)
        /\ req_t = NullReq
        /\ sender_t = NullNode
        /\ pendingInvos_t = {}
        /\ now_t = timeOracle
        (* Process n *)
        /\ req = [self \in Nodes \ {head, tail} |-> NullReq]
        /\ sender = [self \in Nodes \ {head, tail} |-> NullNode]
        /\ now = [self \in Nodes \ {head, tail} |-> timeOracle]
        /\ pendingInvos = [self \in Nodes \ {head, tail} |-> {}]
        (* Process perObj *)
        /\ submittedOps = [self \in Objects |-> {}]
        /\ writes = [self \in Objects |-> {}]
        /\ reads = [self \in Objects |-> {}]
        /\ read = [self \in Objects |-> NullReq]
        /\ edges = [self \in Objects |-> {}]
        /\ clients = [self \in Objects |-> Clients]
        /\ match = [self \in Objects |-> NullReq]
        /\ cli = [self \in Objects |-> NullClient]
        /\ pc = [self \in ProcSet |-> CASE self = "initClient" -> "initializeObj"
                                        [] self \in nonInitClients -> "waitForInit"
                                        [] self = "head" -> "listen_h"
                                        [] self = "tail" -> "listen_t"
                                        [] self \in Nodes \ {head, tail} -> "listen"
                                        [] self \in Objects -> "awaitTermination"]

initializeObj == /\ pc["initClient"] = "initializeObj"
                 /\ IF uninitializedObjs /= {}
                       THEN /\ initObj' = (CHOOSE o \in uninitializedObjs: TRUE)
                            /\ msgQs' = [msgQs EXCEPT ![<<initClient, head>>] = Append(@, ([callType |-> WRITE_INV,
                                                                                            uniqueId |-> uniqueId_cinit,
                                                                                            startTs |-> NullTs,
                                                                                            commitTs |-> NullTs,
                                                                                            op |-> [obj |-> initObj',
                                                                                                    uniqueId |-> uniqueId_cinit,
                                                                                                    writeStartTs |-> NullTs,
                                                                                                    writeCommitTs |-> NullTs,
                                                                                                    commitStatus |-> DIRTY]]))]
                            /\ uninitializedObjs' = uninitializedObjs \ {initObj'}
                            /\ uniqueId_cinit' = Increment(uniqueId_cinit)
                            /\ pc' = [pc EXCEPT !["initClient"] = "waitForInit_"]
                            /\ start' = start
                       ELSE /\ start' = TRUE
                            /\ pc' = [pc EXCEPT !["initClient"] = "concurrentOps_init"]
                            /\ UNCHANGED << msgQs, uninitializedObjs, initObj, 
                                            uniqueId_cinit >>
                 /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedWriteOps, 
                                 allSubmittedReadOps, terminatedYet, 
                                 initClient, nonInitClients, timeOracle, 
                                 isLinearizable, objs_init, obj_init, 
                                 actions_init, action_init, gateway_cinit, 
                                 msg_cinit, sentOps_init, recvdOps_init, objs, 
                                 obj, actions, action, gateway_c, msg_c, 
                                 uniqueId, sentOps, recvdOps, req_h, sender_h, 
                                 pendingInvos_h, now_h, req_t, sender_t, 
                                 pendingInvos_t, now_t, req, sender, now, 
                                 pendingInvos, submittedOps, writes, reads, 
                                 read, edges, clients, match, cli >>

waitForInit_ == /\ pc["initClient"] = "waitForInit_"
                /\ msgQs[<<head, initClient>>] /= << >>
                /\ msg_cinit' = Head(msgQs[<<head, initClient>>])
                /\ msgQs' = [msgQs EXCEPT ![<<head, initClient>>] = Tail(@)]
                /\ IF msg_cinit'.callType = WRITE_RESP
                      THEN /\ allSubmittedWriteOps' = [allSubmittedWriteOps EXCEPT ![msg_cinit'.op.obj] = allSubmittedWriteOps[msg_cinit'.op.obj] \cup {msg_cinit'}]
                           /\ UNCHANGED allSubmittedReadOps
                      ELSE /\ allSubmittedReadOps' = [allSubmittedReadOps EXCEPT ![msg_cinit'.op.obj] = allSubmittedReadOps[msg_cinit'.op.obj] \cup {msg_cinit'}]
                           /\ UNCHANGED allSubmittedWriteOps
                /\ pc' = [pc EXCEPT !["initClient"] = "initializeObj"]
                /\ UNCHANGED << objLogs, objTotalOrders, terminatedYet, 
                                initClient, nonInitClients, start, timeOracle, 
                                isLinearizable, uninitializedObjs, initObj, 
                                objs_init, obj_init, actions_init, action_init, 
                                gateway_cinit, uniqueId_cinit, sentOps_init, 
                                recvdOps_init, objs, obj, actions, action, 
                                gateway_c, msg_c, uniqueId, sentOps, recvdOps, 
                                req_h, sender_h, pendingInvos_h, now_h, req_t, 
                                sender_t, pendingInvos_t, now_t, req, sender, 
                                now, pendingInvos, submittedOps, writes, reads, 
                                read, edges, clients, match, cli >>

concurrentOps_init == /\ pc["initClient"] = "concurrentOps_init"
                      /\ IF objs_init /= {}
                            THEN /\ obj_init' = (CHOOSE o \in objs_init: TRUE)
                                 /\ objs_init' = objs_init \ {obj_init'}
                                 /\ actions_init' = {WRITE_INV, READ_INV}
                                 /\ pc' = [pc EXCEPT !["initClient"] = "readOrWrite_init"]
                            ELSE /\ pc' = [pc EXCEPT !["initClient"] = "waitForOps_init"]
                                 /\ UNCHANGED << objs_init, obj_init, 
                                                 actions_init >>
                      /\ UNCHANGED << msgQs, objLogs, objTotalOrders, 
                                      allSubmittedWriteOps, 
                                      allSubmittedReadOps, terminatedYet, 
                                      initClient, nonInitClients, start, 
                                      timeOracle, isLinearizable, 
                                      uninitializedObjs, initObj, action_init, 
                                      gateway_cinit, msg_cinit, uniqueId_cinit, 
                                      sentOps_init, recvdOps_init, objs, obj, 
                                      actions, action, gateway_c, msg_c, 
                                      uniqueId, sentOps, recvdOps, req_h, 
                                      sender_h, pendingInvos_h, now_h, req_t, 
                                      sender_t, pendingInvos_t, now_t, req, 
                                      sender, now, pendingInvos, submittedOps, 
                                      writes, reads, read, edges, clients, 
                                      match, cli >>

readOrWrite_init == /\ pc["initClient"] = "readOrWrite_init"
                    /\ IF actions_init /= {}
                          THEN /\ action_init' = (CHOOSE a \in actions_init: TRUE)
                               /\ actions_init' = actions_init \ {action_init'}
                               /\ msgQs' = [msgQs EXCEPT ![<<initClient, head>>] = Append(@, ([callType |-> action_init',
                                                                                               uniqueId |-> uniqueId_cinit,
                                                                                               startTs |-> NullTs,
                                                                                               commitTs |-> NullTs,
                                                                                               op |-> [obj |-> obj_init,
                                                                                                       uniqueId |-> uniqueId_cinit,
                                                                                                       writeStartTs |-> NullTs,
                                                                                                       writeCommitTs |-> NullTs,
                                                                                                       commitStatus |-> IF action_init' = WRITE_INV
                                                                                                                           THEN DIRTY
                                                                                                                           ELSE NullCommitStatus]]))]
                               /\ uniqueId_cinit' = Increment(uniqueId_cinit)
                               /\ sentOps_init' = sentOps_init + 1
                               /\ pc' = [pc EXCEPT !["initClient"] = "readOrWrite_init"]
                          ELSE /\ pc' = [pc EXCEPT !["initClient"] = "concurrentOps_init"]
                               /\ UNCHANGED << msgQs, actions_init, 
                                               action_init, uniqueId_cinit, 
                                               sentOps_init >>
                    /\ UNCHANGED << objLogs, objTotalOrders, 
                                    allSubmittedWriteOps, allSubmittedReadOps, 
                                    terminatedYet, initClient, nonInitClients, 
                                    start, timeOracle, isLinearizable, 
                                    uninitializedObjs, initObj, objs_init, 
                                    obj_init, gateway_cinit, msg_cinit, 
                                    recvdOps_init, objs, obj, actions, action, 
                                    gateway_c, msg_c, uniqueId, sentOps, 
                                    recvdOps, req_h, sender_h, pendingInvos_h, 
                                    now_h, req_t, sender_t, pendingInvos_t, 
                                    now_t, req, sender, now, pendingInvos, 
                                    submittedOps, writes, reads, read, edges, 
                                    clients, match, cli >>

waitForOps_init == /\ pc["initClient"] = "waitForOps_init"
                   /\ IF recvdOps_init < sentOps_init
                         THEN /\ pc' = [pc EXCEPT !["initClient"] = "block_init"]
                         ELSE /\ pc' = [pc EXCEPT !["initClient"] = "terminate_init"]
                   /\ UNCHANGED << msgQs, objLogs, objTotalOrders, 
                                   allSubmittedWriteOps, allSubmittedReadOps, 
                                   terminatedYet, initClient, nonInitClients, 
                                   start, timeOracle, isLinearizable, 
                                   uninitializedObjs, initObj, objs_init, 
                                   obj_init, actions_init, action_init, 
                                   gateway_cinit, msg_cinit, uniqueId_cinit, 
                                   sentOps_init, recvdOps_init, objs, obj, 
                                   actions, action, gateway_c, msg_c, uniqueId, 
                                   sentOps, recvdOps, req_h, sender_h, 
                                   pendingInvos_h, now_h, req_t, sender_t, 
                                   pendingInvos_t, now_t, req, sender, now, 
                                   pendingInvos, submittedOps, writes, reads, 
                                   read, edges, clients, match, cli >>

block_init == /\ pc["initClient"] = "block_init"
              /\ \E temp \in {s \in SendersTo(initClient): msgQs[<<s, initClient>>] /= << >>}:
                   gateway_cinit' = temp
              /\ pc' = [pc EXCEPT !["initClient"] = "moreblock_init"]
              /\ UNCHANGED << msgQs, objLogs, objTotalOrders, 
                              allSubmittedWriteOps, allSubmittedReadOps, 
                              terminatedYet, initClient, nonInitClients, start, 
                              timeOracle, isLinearizable, uninitializedObjs, 
                              initObj, objs_init, obj_init, actions_init, 
                              action_init, msg_cinit, uniqueId_cinit, 
                              sentOps_init, recvdOps_init, objs, obj, actions, 
                              action, gateway_c, msg_c, uniqueId, sentOps, 
                              recvdOps, req_h, sender_h, pendingInvos_h, now_h, 
                              req_t, sender_t, pendingInvos_t, now_t, req, 
                              sender, now, pendingInvos, submittedOps, writes, 
                              reads, read, edges, clients, match, cli >>

moreblock_init == /\ pc["initClient"] = "moreblock_init"
                  /\ msgQs[<<gateway_cinit, initClient>>] /= << >>
                  /\ pc' = [pc EXCEPT !["initClient"] = "recv_init"]
                  /\ UNCHANGED << msgQs, objLogs, objTotalOrders, 
                                  allSubmittedWriteOps, allSubmittedReadOps, 
                                  terminatedYet, initClient, nonInitClients, 
                                  start, timeOracle, isLinearizable, 
                                  uninitializedObjs, initObj, objs_init, 
                                  obj_init, actions_init, action_init, 
                                  gateway_cinit, msg_cinit, uniqueId_cinit, 
                                  sentOps_init, recvdOps_init, objs, obj, 
                                  actions, action, gateway_c, msg_c, uniqueId, 
                                  sentOps, recvdOps, req_h, sender_h, 
                                  pendingInvos_h, now_h, req_t, sender_t, 
                                  pendingInvos_t, now_t, req, sender, now, 
                                  pendingInvos, submittedOps, writes, reads, 
                                  read, edges, clients, match, cli >>

recv_init == /\ pc["initClient"] = "recv_init"
             /\ msg_cinit' = Head(msgQs[<<gateway_cinit, initClient>>])
             /\ msgQs' = [msgQs EXCEPT ![<<gateway_cinit, initClient>>] = Tail(@)]
             /\ pc' = [pc EXCEPT !["initClient"] = "add_init"]
             /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedWriteOps, 
                             allSubmittedReadOps, terminatedYet, initClient, 
                             nonInitClients, start, timeOracle, isLinearizable, 
                             uninitializedObjs, initObj, objs_init, obj_init, 
                             actions_init, action_init, gateway_cinit, 
                             uniqueId_cinit, sentOps_init, recvdOps_init, objs, 
                             obj, actions, action, gateway_c, msg_c, uniqueId, 
                             sentOps, recvdOps, req_h, sender_h, 
                             pendingInvos_h, now_h, req_t, sender_t, 
                             pendingInvos_t, now_t, req, sender, now, 
                             pendingInvos, submittedOps, writes, reads, read, 
                             edges, clients, match, cli >>

add_init == /\ pc["initClient"] = "add_init"
            /\ IF msg_cinit.callType = WRITE_RESP
                  THEN /\ allSubmittedWriteOps' = [allSubmittedWriteOps EXCEPT ![msg_cinit.op.obj] = allSubmittedWriteOps[msg_cinit.op.obj] \cup {msg_cinit}]
                       /\ UNCHANGED allSubmittedReadOps
                  ELSE /\ allSubmittedReadOps' = [allSubmittedReadOps EXCEPT ![msg_cinit.op.obj] = allSubmittedReadOps[msg_cinit.op.obj] \cup {msg_cinit}]
                       /\ UNCHANGED allSubmittedWriteOps
            /\ pc' = [pc EXCEPT !["initClient"] = "increment_init"]
            /\ UNCHANGED << msgQs, objLogs, objTotalOrders, terminatedYet, 
                            initClient, nonInitClients, start, timeOracle, 
                            isLinearizable, uninitializedObjs, initObj, 
                            objs_init, obj_init, actions_init, action_init, 
                            gateway_cinit, msg_cinit, uniqueId_cinit, 
                            sentOps_init, recvdOps_init, objs, obj, actions, 
                            action, gateway_c, msg_c, uniqueId, sentOps, 
                            recvdOps, req_h, sender_h, pendingInvos_h, now_h, 
                            req_t, sender_t, pendingInvos_t, now_t, req, 
                            sender, now, pendingInvos, submittedOps, writes, 
                            reads, read, edges, clients, match, cli >>

increment_init == /\ pc["initClient"] = "increment_init"
                  /\ recvdOps_init' = recvdOps_init + 1
                  /\ pc' = [pc EXCEPT !["initClient"] = "waitForOps_init"]
                  /\ UNCHANGED << msgQs, objLogs, objTotalOrders, 
                                  allSubmittedWriteOps, allSubmittedReadOps, 
                                  terminatedYet, initClient, nonInitClients, 
                                  start, timeOracle, isLinearizable, 
                                  uninitializedObjs, initObj, objs_init, 
                                  obj_init, actions_init, action_init, 
                                  gateway_cinit, msg_cinit, uniqueId_cinit, 
                                  sentOps_init, objs, obj, actions, action, 
                                  gateway_c, msg_c, uniqueId, sentOps, 
                                  recvdOps, req_h, sender_h, pendingInvos_h, 
                                  now_h, req_t, sender_t, pendingInvos_t, 
                                  now_t, req, sender, now, pendingInvos, 
                                  submittedOps, writes, reads, read, edges, 
                                  clients, match, cli >>

terminate_init == /\ pc["initClient"] = "terminate_init"
                  /\ terminatedYet' = [terminatedYet EXCEPT ![initClient] = TRUE]
                  /\ pc' = [pc EXCEPT !["initClient"] = "Done"]
                  /\ UNCHANGED << msgQs, objLogs, objTotalOrders, 
                                  allSubmittedWriteOps, allSubmittedReadOps, 
                                  initClient, nonInitClients, start, 
                                  timeOracle, isLinearizable, 
                                  uninitializedObjs, initObj, objs_init, 
                                  obj_init, actions_init, action_init, 
                                  gateway_cinit, msg_cinit, uniqueId_cinit, 
                                  sentOps_init, recvdOps_init, objs, obj, 
                                  actions, action, gateway_c, msg_c, uniqueId, 
                                  sentOps, recvdOps, req_h, sender_h, 
                                  pendingInvos_h, now_h, req_t, sender_t, 
                                  pendingInvos_t, now_t, req, sender, now, 
                                  pendingInvos, submittedOps, writes, reads, 
                                  read, edges, clients, match, cli >>

iclient == initializeObj \/ waitForInit_ \/ concurrentOps_init
              \/ readOrWrite_init \/ waitForOps_init \/ block_init
              \/ moreblock_init \/ recv_init \/ add_init \/ increment_init
              \/ terminate_init

waitForInit(self) == /\ pc[self] = "waitForInit"
                     /\ start = TRUE
                     /\ pc' = [pc EXCEPT ![self] = "concurrentOps"]
                     /\ UNCHANGED << msgQs, objLogs, objTotalOrders, 
                                     allSubmittedWriteOps, allSubmittedReadOps, 
                                     terminatedYet, initClient, nonInitClients, 
                                     start, timeOracle, isLinearizable, 
                                     uninitializedObjs, initObj, objs_init, 
                                     obj_init, actions_init, action_init, 
                                     gateway_cinit, msg_cinit, uniqueId_cinit, 
                                     sentOps_init, recvdOps_init, objs, obj, 
                                     actions, action, gateway_c, msg_c, 
                                     uniqueId, sentOps, recvdOps, req_h, 
                                     sender_h, pendingInvos_h, now_h, req_t, 
                                     sender_t, pendingInvos_t, now_t, req, 
                                     sender, now, pendingInvos, submittedOps, 
                                     writes, reads, read, edges, clients, 
                                     match, cli >>

concurrentOps(self) == /\ pc[self] = "concurrentOps"
                       /\ IF objs[self] /= {}
                             THEN /\ obj' = [obj EXCEPT ![self] = CHOOSE o \in objs[self]: TRUE]
                                  /\ objs' = [objs EXCEPT ![self] = objs[self] \ {obj'[self]}]
                                  /\ pc' = [pc EXCEPT ![self] = "readOrWrite"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "waitForOps"]
                                  /\ UNCHANGED << objs, obj >>
                       /\ UNCHANGED << msgQs, objLogs, objTotalOrders, 
                                       allSubmittedWriteOps, 
                                       allSubmittedReadOps, terminatedYet, 
                                       initClient, nonInitClients, start, 
                                       timeOracle, isLinearizable, 
                                       uninitializedObjs, initObj, objs_init, 
                                       obj_init, actions_init, action_init, 
                                       gateway_cinit, msg_cinit, 
                                       uniqueId_cinit, sentOps_init, 
                                       recvdOps_init, actions, action, 
                                       gateway_c, msg_c, uniqueId, sentOps, 
                                       recvdOps, req_h, sender_h, 
                                       pendingInvos_h, now_h, req_t, sender_t, 
                                       pendingInvos_t, now_t, req, sender, now, 
                                       pendingInvos, submittedOps, writes, 
                                       reads, read, edges, clients, match, cli >>

readOrWrite(self) == /\ pc[self] = "readOrWrite"
                     /\ IF actions[self] /= {}
                           THEN /\ action' = [action EXCEPT ![self] = CHOOSE a \in actions[self]: TRUE]
                                /\ actions' = [actions EXCEPT ![self] = actions[self] \ {action'[self]}]
                                /\ msgQs' = [msgQs EXCEPT ![<<self, (IF action'[self] = WRITE_INV THEN head ELSE CHOOSE n \in Nodes: n /= head)>>] = Append(@, ([   callType |-> action'[self],
                                                                                                                                                                    uniqueId |-> uniqueId[self],
                                                                                                                                                                    startTs |-> NullTs,
                                                                                                                                                                    commitTs |-> NullTs,
                                                                                                                                                                    op |-> [obj |-> obj[self],
                                                                                                                                                                            uniqueId |-> uniqueId[self],
                                                                                                                                                                            writeStartTs |-> NullTs,
                                                                                                                                                                            writeCommitTs |-> NullTs,
                                                                                                                                                                            commitStatus |-> IF action'[self] = WRITE_INV
                                                                                                                                                                                                THEN DIRTY
                                                                                                                                                                                                ELSE NullCommitStatus]]))]
                                /\ uniqueId' = [uniqueId EXCEPT ![self] = Increment(uniqueId[self])]
                                /\ sentOps' = [sentOps EXCEPT ![self] = sentOps[self] + 1]
                                /\ pc' = [pc EXCEPT ![self] = "readOrWrite"]
                           ELSE /\ actions' = [actions EXCEPT ![self] = {WRITE_INV, READ_INV}]
                                /\ pc' = [pc EXCEPT ![self] = "concurrentOps"]
                                /\ UNCHANGED << msgQs, action, uniqueId, 
                                                sentOps >>
                     /\ UNCHANGED << objLogs, objTotalOrders, 
                                     allSubmittedWriteOps, allSubmittedReadOps, 
                                     terminatedYet, initClient, nonInitClients, 
                                     start, timeOracle, isLinearizable, 
                                     uninitializedObjs, initObj, objs_init, 
                                     obj_init, actions_init, action_init, 
                                     gateway_cinit, msg_cinit, uniqueId_cinit, 
                                     sentOps_init, recvdOps_init, objs, obj, 
                                     gateway_c, msg_c, recvdOps, req_h, 
                                     sender_h, pendingInvos_h, now_h, req_t, 
                                     sender_t, pendingInvos_t, now_t, req, 
                                     sender, now, pendingInvos, submittedOps, 
                                     writes, reads, read, edges, clients, 
                                     match, cli >>

waitForOps(self) == /\ pc[self] = "waitForOps"
                    /\ IF recvdOps[self] < sentOps[self]
                          THEN /\ \E temp \in {s \in SendersTo(self): msgQs[<<s, self>>] /= << >>}:
                                    gateway_c' = [gateway_c EXCEPT ![self] = temp]
                               /\ msgQs[<<gateway_c'[self], self>>] /= << >>
                               /\ msg_c' = [msg_c EXCEPT ![self] = Head(msgQs[<<gateway_c'[self], self>>])]
                               /\ msgQs' = [msgQs EXCEPT ![<<gateway_c'[self], self>>] = Tail(@)]
                               /\ IF msg_c'[self].callType = WRITE_RESP
                                     THEN /\ allSubmittedWriteOps' = [allSubmittedWriteOps EXCEPT ![msg_c'[self].op.obj] = allSubmittedWriteOps[msg_c'[self].op.obj] \cup {msg_c'[self]}]
                                          /\ UNCHANGED allSubmittedReadOps
                                     ELSE /\ allSubmittedReadOps' = [allSubmittedReadOps EXCEPT ![msg_c'[self].op.obj] = allSubmittedReadOps[msg_c'[self].op.obj] \cup {msg_c'[self]}]
                                          /\ UNCHANGED allSubmittedWriteOps
                               /\ Assert((msg_c'[self].uniqueId[1] = self), 
                                         "Failure of assertion at line 319, column 13.")
                               /\ recvdOps' = [recvdOps EXCEPT ![self] = recvdOps[self] + 1]
                               /\ pc' = [pc EXCEPT ![self] = "waitForOps"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "terminate"]
                               /\ UNCHANGED << msgQs, allSubmittedWriteOps, 
                                               allSubmittedReadOps, gateway_c, 
                                               msg_c, recvdOps >>
                    /\ UNCHANGED << objLogs, objTotalOrders, terminatedYet, 
                                    initClient, nonInitClients, start, 
                                    timeOracle, isLinearizable, 
                                    uninitializedObjs, initObj, objs_init, 
                                    obj_init, actions_init, action_init, 
                                    gateway_cinit, msg_cinit, uniqueId_cinit, 
                                    sentOps_init, recvdOps_init, objs, obj, 
                                    actions, action, uniqueId, sentOps, req_h, 
                                    sender_h, pendingInvos_h, now_h, req_t, 
                                    sender_t, pendingInvos_t, now_t, req, 
                                    sender, now, pendingInvos, submittedOps, 
                                    writes, reads, read, edges, clients, match, 
                                    cli >>

terminate(self) == /\ pc[self] = "terminate"
                   /\ terminatedYet' = [terminatedYet EXCEPT ![self] = TRUE]
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << msgQs, objLogs, objTotalOrders, 
                                   allSubmittedWriteOps, allSubmittedReadOps, 
                                   initClient, nonInitClients, start, 
                                   timeOracle, isLinearizable, 
                                   uninitializedObjs, initObj, objs_init, 
                                   obj_init, actions_init, action_init, 
                                   gateway_cinit, msg_cinit, uniqueId_cinit, 
                                   sentOps_init, recvdOps_init, objs, obj, 
                                   actions, action, gateway_c, msg_c, uniqueId, 
                                   sentOps, recvdOps, req_h, sender_h, 
                                   pendingInvos_h, now_h, req_t, sender_t, 
                                   pendingInvos_t, now_t, req, sender, now, 
                                   pendingInvos, submittedOps, writes, reads, 
                                   read, edges, clients, match, cli >>

c(self) == waitForInit(self) \/ concurrentOps(self) \/ readOrWrite(self)
              \/ waitForOps(self) \/ terminate(self)

listen_h == /\ pc["head"] = "listen_h"
            /\ \E temp \in {s \in SendersTo(head): msgQs[<<s, head>>] /= << >>}:
                 sender_h' = temp
            /\ pc' = [pc EXCEPT !["head"] = "incomingMsg_h"]
            /\ UNCHANGED << msgQs, objLogs, objTotalOrders, 
                            allSubmittedWriteOps, allSubmittedReadOps, 
                            terminatedYet, initClient, nonInitClients, start, 
                            timeOracle, isLinearizable, uninitializedObjs, 
                            initObj, objs_init, obj_init, actions_init, 
                            action_init, gateway_cinit, msg_cinit, 
                            uniqueId_cinit, sentOps_init, recvdOps_init, objs, 
                            obj, actions, action, gateway_c, msg_c, uniqueId, 
                            sentOps, recvdOps, req_h, pendingInvos_h, now_h, 
                            req_t, sender_t, pendingInvos_t, now_t, req, 
                            sender, now, pendingInvos, submittedOps, writes, 
                            reads, read, edges, clients, match, cli >>

incomingMsg_h == /\ pc["head"] = "incomingMsg_h"
                 /\ msgQs[<<sender_h, head>>] /= << >>
                 /\ req_h' = Head(msgQs[<<sender_h, head>>])
                 /\ msgQs' = [msgQs EXCEPT ![<<sender_h, head>>] = Tail(@)]
                 /\ IF req_h'.callType = READ_INV
                       THEN /\ IF IsDirty(head, req_h'.op.obj)
                                  THEN /\ pc' = [pc EXCEPT !["head"] = "apportionQ_h"]
                                       /\ UNCHANGED << timeOracle, now_h >>
                                  ELSE /\ now_h' = timeOracle
                                       /\ timeOracle' = timeOracle + 1
                                       /\ pc' = [pc EXCEPT !["head"] = "addReadTO_h"]
                            /\ UNCHANGED objLogs
                       ELSE /\ IF req_h'.callType = READ_RESP
                                  THEN /\ pc' = [pc EXCEPT !["head"] = "readResp_h"]
                                       /\ UNCHANGED << objLogs, timeOracle, 
                                                       now_h >>
                                  ELSE /\ IF req_h'.callType = WRITE_INV
                                             THEN /\ now_h' = timeOracle
                                                  /\ timeOracle' = timeOracle + 1
                                                  /\ pc' = [pc EXCEPT !["head"] = "dirtyWrite_h"]
                                                  /\ UNCHANGED objLogs
                                             ELSE /\ objLogs' = [objLogs EXCEPT ![head][req_h'.op.obj] = CommitDirtyVersion(@, req_h'.op)]
                                                  /\ pc' = [pc EXCEPT !["head"] = "respToClient"]
                                                  /\ UNCHANGED << timeOracle, 
                                                                  now_h >>
                 /\ UNCHANGED << objTotalOrders, allSubmittedWriteOps, 
                                 allSubmittedReadOps, terminatedYet, 
                                 initClient, nonInitClients, start, 
                                 isLinearizable, uninitializedObjs, initObj, 
                                 objs_init, obj_init, actions_init, 
                                 action_init, gateway_cinit, msg_cinit, 
                                 uniqueId_cinit, sentOps_init, recvdOps_init, 
                                 objs, obj, actions, action, gateway_c, msg_c, 
                                 uniqueId, sentOps, recvdOps, sender_h, 
                                 pendingInvos_h, req_t, sender_t, 
                                 pendingInvos_t, now_t, req, sender, now, 
                                 pendingInvos, submittedOps, writes, reads, 
                                 read, edges, clients, match, cli >>

apportionQ_h == /\ pc["head"] = "apportionQ_h"
                /\ msgQs' = [msgQs EXCEPT ![<<head, tail>>] = Append(@, req_h)]
                /\ pendingInvos_h' = (pendingInvos_h \cup {<<(req_h.uniqueId), sender_h>>})
                /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
                /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedWriteOps, 
                                allSubmittedReadOps, terminatedYet, initClient, 
                                nonInitClients, start, timeOracle, 
                                isLinearizable, uninitializedObjs, initObj, 
                                objs_init, obj_init, actions_init, action_init, 
                                gateway_cinit, msg_cinit, uniqueId_cinit, 
                                sentOps_init, recvdOps_init, objs, obj, 
                                actions, action, gateway_c, msg_c, uniqueId, 
                                sentOps, recvdOps, req_h, sender_h, now_h, 
                                req_t, sender_t, pendingInvos_t, now_t, req, 
                                sender, now, pendingInvos, submittedOps, 
                                writes, reads, read, edges, clients, match, 
                                cli >>

addReadTO_h == /\ pc["head"] = "addReadTO_h"
               /\ req_h' = [ callType |-> READ_RESP,
                             uniqueId |-> req_h.uniqueId,
                             startTs |-> timeOracle,
                             commitTs |-> timeOracle,
                             op |-> Read(head, req_h.op.obj)]
               /\ objTotalOrders' = [objTotalOrders EXCEPT ![req_h'.op.obj] = Cons(req_h', @)]
               /\ pc' = [pc EXCEPT !["head"] = "respFromHead"]
               /\ UNCHANGED << msgQs, objLogs, allSubmittedWriteOps, 
                               allSubmittedReadOps, terminatedYet, initClient, 
                               nonInitClients, start, timeOracle, 
                               isLinearizable, uninitializedObjs, initObj, 
                               objs_init, obj_init, actions_init, action_init, 
                               gateway_cinit, msg_cinit, uniqueId_cinit, 
                               sentOps_init, recvdOps_init, objs, obj, actions, 
                               action, gateway_c, msg_c, uniqueId, sentOps, 
                               recvdOps, sender_h, pendingInvos_h, now_h, 
                               req_t, sender_t, pendingInvos_t, now_t, req, 
                               sender, now, pendingInvos, submittedOps, writes, 
                               reads, read, edges, clients, match, cli >>

respFromHead == /\ pc["head"] = "respFromHead"
                /\ msgQs' = [msgQs EXCEPT ![<<head, sender_h>>] = Append(@, req_h)]
                /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
                /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedWriteOps, 
                                allSubmittedReadOps, terminatedYet, initClient, 
                                nonInitClients, start, timeOracle, 
                                isLinearizable, uninitializedObjs, initObj, 
                                objs_init, obj_init, actions_init, action_init, 
                                gateway_cinit, msg_cinit, uniqueId_cinit, 
                                sentOps_init, recvdOps_init, objs, obj, 
                                actions, action, gateway_c, msg_c, uniqueId, 
                                sentOps, recvdOps, req_h, sender_h, 
                                pendingInvos_h, now_h, req_t, sender_t, 
                                pendingInvos_t, now_t, req, sender, now, 
                                pendingInvos, submittedOps, writes, reads, 
                                read, edges, clients, match, cli >>

readResp_h == /\ pc["head"] = "readResp_h"
              /\ msgQs' = [msgQs EXCEPT ![<<head, (Find(pendingInvos_h, req_h.uniqueId))>>] = Append(@, req_h)]
              /\ pendingInvos_h' = pendingInvos_h \ {FindPair(pendingInvos_h, (req_h.uniqueId))}
              /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
              /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedWriteOps, 
                              allSubmittedReadOps, terminatedYet, initClient, 
                              nonInitClients, start, timeOracle, 
                              isLinearizable, uninitializedObjs, initObj, 
                              objs_init, obj_init, actions_init, action_init, 
                              gateway_cinit, msg_cinit, uniqueId_cinit, 
                              sentOps_init, recvdOps_init, objs, obj, actions, 
                              action, gateway_c, msg_c, uniqueId, sentOps, 
                              recvdOps, req_h, sender_h, now_h, req_t, 
                              sender_t, pendingInvos_t, now_t, req, sender, 
                              now, pendingInvos, submittedOps, writes, reads, 
                              read, edges, clients, match, cli >>

dirtyWrite_h == /\ pc["head"] = "dirtyWrite_h"
                /\ req_h' = [req_h EXCEPT    !.startTs = now_h,
                                             !.op.writeStartTs = now_h,
                                             !.op.commitStatus = DIRTY]
                /\ objLogs' = [objLogs EXCEPT ![head][(req_h'.op).obj] = Cons((req_h'.op), @)]
                /\ pc' = [pc EXCEPT !["head"] = "propagate_h"]
                /\ UNCHANGED << msgQs, objTotalOrders, allSubmittedWriteOps, 
                                allSubmittedReadOps, terminatedYet, initClient, 
                                nonInitClients, start, timeOracle, 
                                isLinearizable, uninitializedObjs, initObj, 
                                objs_init, obj_init, actions_init, action_init, 
                                gateway_cinit, msg_cinit, uniqueId_cinit, 
                                sentOps_init, recvdOps_init, objs, obj, 
                                actions, action, gateway_c, msg_c, uniqueId, 
                                sentOps, recvdOps, sender_h, pendingInvos_h, 
                                now_h, req_t, sender_t, pendingInvos_t, now_t, 
                                req, sender, now, pendingInvos, submittedOps, 
                                writes, reads, read, edges, clients, match, 
                                cli >>

propagate_h == /\ pc["head"] = "propagate_h"
               /\ msgQs' = [msgQs EXCEPT ![<<head, (Successors[head])>>] = Append(@, req_h)]
               /\ pendingInvos_h' = (pendingInvos_h \cup {<<(req_h.uniqueId), sender_h>>})
               /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
               /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedWriteOps, 
                               allSubmittedReadOps, terminatedYet, initClient, 
                               nonInitClients, start, timeOracle, 
                               isLinearizable, uninitializedObjs, initObj, 
                               objs_init, obj_init, actions_init, action_init, 
                               gateway_cinit, msg_cinit, uniqueId_cinit, 
                               sentOps_init, recvdOps_init, objs, obj, actions, 
                               action, gateway_c, msg_c, uniqueId, sentOps, 
                               recvdOps, req_h, sender_h, now_h, req_t, 
                               sender_t, pendingInvos_t, now_t, req, sender, 
                               now, pendingInvos, submittedOps, writes, reads, 
                               read, edges, clients, match, cli >>

respToClient == /\ pc["head"] = "respToClient"
                /\ msgQs' = [msgQs EXCEPT ![<<head, (Find(pendingInvos_h, req_h.uniqueId))>>] = Append(@, req_h)]
                /\ pendingInvos_h' = pendingInvos_h \ {FindPair(pendingInvos_h, (req_h.uniqueId))}
                /\ pc' = [pc EXCEPT !["head"] = "listen_h"]
                /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedWriteOps, 
                                allSubmittedReadOps, terminatedYet, initClient, 
                                nonInitClients, start, timeOracle, 
                                isLinearizable, uninitializedObjs, initObj, 
                                objs_init, obj_init, actions_init, action_init, 
                                gateway_cinit, msg_cinit, uniqueId_cinit, 
                                sentOps_init, recvdOps_init, objs, obj, 
                                actions, action, gateway_c, msg_c, uniqueId, 
                                sentOps, recvdOps, req_h, sender_h, now_h, 
                                req_t, sender_t, pendingInvos_t, now_t, req, 
                                sender, now, pendingInvos, submittedOps, 
                                writes, reads, read, edges, clients, match, 
                                cli >>

he == listen_h \/ incomingMsg_h \/ apportionQ_h \/ addReadTO_h
         \/ respFromHead \/ readResp_h \/ dirtyWrite_h \/ propagate_h
         \/ respToClient

listen_t == /\ pc["tail"] = "listen_t"
            /\ \E temp \in {s \in SendersTo(tail) : msgQs[<<s, tail>>] /= << >>}:
                 sender_t' = temp
            /\ pc' = [pc EXCEPT !["tail"] = "incomingMsg_t"]
            /\ UNCHANGED << msgQs, objLogs, objTotalOrders, 
                            allSubmittedWriteOps, allSubmittedReadOps, 
                            terminatedYet, initClient, nonInitClients, start, 
                            timeOracle, isLinearizable, uninitializedObjs, 
                            initObj, objs_init, obj_init, actions_init, 
                            action_init, gateway_cinit, msg_cinit, 
                            uniqueId_cinit, sentOps_init, recvdOps_init, objs, 
                            obj, actions, action, gateway_c, msg_c, uniqueId, 
                            sentOps, recvdOps, req_h, sender_h, pendingInvos_h, 
                            now_h, req_t, pendingInvos_t, now_t, req, sender, 
                            now, pendingInvos, submittedOps, writes, reads, 
                            read, edges, clients, match, cli >>

incomingMsg_t == /\ pc["tail"] = "incomingMsg_t"
                 /\ msgQs[<<sender_t, tail>>] /= << >>
                 /\ req_t' = Head(msgQs[<<sender_t, tail>>])
                 /\ msgQs' = [msgQs EXCEPT ![<<sender_t, tail>>] = Tail(@)]
                 /\ IF req_t'.callType = READ_INV
                       THEN /\ now_t' = timeOracle
                            /\ timeOracle' = timeOracle + 1
                            /\ pc' = [pc EXCEPT !["tail"] = "addReadTO_t"]
                            /\ UNCHANGED objLogs
                       ELSE /\ now_t' = timeOracle
                            /\ timeOracle' = timeOracle + 1
                            /\ objLogs' = [objLogs EXCEPT ![tail][([req_t'.op EXCEPT  !.writeCommitTs = now_t',
                                                                                      !.commitStatus = CLEAN]).obj] = Cons(([req_t'.op EXCEPT  !.writeCommitTs = now_t',
                                                                                                                                               !.commitStatus = CLEAN]), @)]
                            /\ pc' = [pc EXCEPT !["tail"] = "addWriteTO_t"]
                 /\ UNCHANGED << objTotalOrders, allSubmittedWriteOps, 
                                 allSubmittedReadOps, terminatedYet, 
                                 initClient, nonInitClients, start, 
                                 isLinearizable, uninitializedObjs, initObj, 
                                 objs_init, obj_init, actions_init, 
                                 action_init, gateway_cinit, msg_cinit, 
                                 uniqueId_cinit, sentOps_init, recvdOps_init, 
                                 objs, obj, actions, action, gateway_c, msg_c, 
                                 uniqueId, sentOps, recvdOps, req_h, sender_h, 
                                 pendingInvos_h, now_h, sender_t, 
                                 pendingInvos_t, req, sender, now, 
                                 pendingInvos, submittedOps, writes, reads, 
                                 read, edges, clients, match, cli >>

addReadTO_t == /\ pc["tail"] = "addReadTO_t"
               /\ req_t' = [ callType |-> READ_RESP,
                             uniqueId |-> req_t.uniqueId,
                             startTs |-> now_t,
                             commitTs |-> now_t,
                             op |-> Read(tail, req_t.op.obj)]
               /\ objTotalOrders' = [objTotalOrders EXCEPT ![req_t'.op.obj] = Cons(req_t', @)]
               /\ pc' = [pc EXCEPT !["tail"] = "respFromSelf_t"]
               /\ UNCHANGED << msgQs, objLogs, allSubmittedWriteOps, 
                               allSubmittedReadOps, terminatedYet, initClient, 
                               nonInitClients, start, timeOracle, 
                               isLinearizable, uninitializedObjs, initObj, 
                               objs_init, obj_init, actions_init, action_init, 
                               gateway_cinit, msg_cinit, uniqueId_cinit, 
                               sentOps_init, recvdOps_init, objs, obj, actions, 
                               action, gateway_c, msg_c, uniqueId, sentOps, 
                               recvdOps, req_h, sender_h, pendingInvos_h, 
                               now_h, sender_t, pendingInvos_t, now_t, req, 
                               sender, now, pendingInvos, submittedOps, writes, 
                               reads, read, edges, clients, match, cli >>

respFromSelf_t == /\ pc["tail"] = "respFromSelf_t"
                  /\ msgQs' = [msgQs EXCEPT ![<<tail, sender_t>>] = Append(@, req_t)]
                  /\ pc' = [pc EXCEPT !["tail"] = "listen_t"]
                  /\ UNCHANGED << objLogs, objTotalOrders, 
                                  allSubmittedWriteOps, allSubmittedReadOps, 
                                  terminatedYet, initClient, nonInitClients, 
                                  start, timeOracle, isLinearizable, 
                                  uninitializedObjs, initObj, objs_init, 
                                  obj_init, actions_init, action_init, 
                                  gateway_cinit, msg_cinit, uniqueId_cinit, 
                                  sentOps_init, recvdOps_init, objs, obj, 
                                  actions, action, gateway_c, msg_c, uniqueId, 
                                  sentOps, recvdOps, req_h, sender_h, 
                                  pendingInvos_h, now_h, req_t, sender_t, 
                                  pendingInvos_t, now_t, req, sender, now, 
                                  pendingInvos, submittedOps, writes, reads, 
                                  read, edges, clients, match, cli >>

addWriteTO_t == /\ pc["tail"] = "addWriteTO_t"
                /\ req_t' = [    callType |-> WRITE_RESP,
                                 uniqueId |-> req_t.uniqueId,
                                 startTs |-> req_t.startTs,
                                 commitTs |-> Read(tail, req_t.op.obj).writeCommitTs,
                                 op |-> Read(tail, req_t.op.obj)]
                /\ objTotalOrders' = [objTotalOrders EXCEPT ![req_t'.op.obj] = Cons(req_t', @)]
                /\ pc' = [pc EXCEPT !["tail"] = "tailAck"]
                /\ UNCHANGED << msgQs, objLogs, allSubmittedWriteOps, 
                                allSubmittedReadOps, terminatedYet, initClient, 
                                nonInitClients, start, timeOracle, 
                                isLinearizable, uninitializedObjs, initObj, 
                                objs_init, obj_init, actions_init, action_init, 
                                gateway_cinit, msg_cinit, uniqueId_cinit, 
                                sentOps_init, recvdOps_init, objs, obj, 
                                actions, action, gateway_c, msg_c, uniqueId, 
                                sentOps, recvdOps, req_h, sender_h, 
                                pendingInvos_h, now_h, sender_t, 
                                pendingInvos_t, now_t, req, sender, now, 
                                pendingInvos, submittedOps, writes, reads, 
                                read, edges, clients, match, cli >>

tailAck == /\ pc["tail"] = "tailAck"
           /\ msgQs' = [msgQs EXCEPT ![<<tail, (Predecessors[tail])>>] = Append(@, req_t)]
           /\ pc' = [pc EXCEPT !["tail"] = "listen_t"]
           /\ UNCHANGED << objLogs, objTotalOrders, allSubmittedWriteOps, 
                           allSubmittedReadOps, terminatedYet, initClient, 
                           nonInitClients, start, timeOracle, isLinearizable, 
                           uninitializedObjs, initObj, objs_init, obj_init, 
                           actions_init, action_init, gateway_cinit, msg_cinit, 
                           uniqueId_cinit, sentOps_init, recvdOps_init, objs, 
                           obj, actions, action, gateway_c, msg_c, uniqueId, 
                           sentOps, recvdOps, req_h, sender_h, pendingInvos_h, 
                           now_h, req_t, sender_t, pendingInvos_t, now_t, req, 
                           sender, now, pendingInvos, submittedOps, writes, 
                           reads, read, edges, clients, match, cli >>

ta == listen_t \/ incomingMsg_t \/ addReadTO_t \/ respFromSelf_t
         \/ addWriteTO_t \/ tailAck

listen(self) == /\ pc[self] = "listen"
                /\ \E temp \in {s \in SendersTo(self) : msgQs[<<s, self>>] /= << >>}:
                     sender' = [sender EXCEPT ![self] = temp]
                /\ pc' = [pc EXCEPT ![self] = "incomingMsg"]
                /\ UNCHANGED << msgQs, objLogs, objTotalOrders, 
                                allSubmittedWriteOps, allSubmittedReadOps, 
                                terminatedYet, initClient, nonInitClients, 
                                start, timeOracle, isLinearizable, 
                                uninitializedObjs, initObj, objs_init, 
                                obj_init, actions_init, action_init, 
                                gateway_cinit, msg_cinit, uniqueId_cinit, 
                                sentOps_init, recvdOps_init, objs, obj, 
                                actions, action, gateway_c, msg_c, uniqueId, 
                                sentOps, recvdOps, req_h, sender_h, 
                                pendingInvos_h, now_h, req_t, sender_t, 
                                pendingInvos_t, now_t, req, now, pendingInvos, 
                                submittedOps, writes, reads, read, edges, 
                                clients, match, cli >>

incomingMsg(self) == /\ pc[self] = "incomingMsg"
                     /\ msgQs[<<sender[self], self>>] /= << >>
                     /\ req' = [req EXCEPT ![self] = Head(msgQs[<<sender[self], self>>])]
                     /\ msgQs' = [msgQs EXCEPT ![<<sender[self], self>>] = Tail(@)]
                     /\ IF req'[self].callType = READ_INV
                           THEN /\ IF IsDirty(self, req'[self].op.obj)
                                      THEN /\ pc' = [pc EXCEPT ![self] = "apportionQ"]
                                           /\ UNCHANGED << timeOracle, now >>
                                      ELSE /\ now' = [now EXCEPT ![self] = timeOracle]
                                           /\ timeOracle' = timeOracle + 1
                                           /\ pc' = [pc EXCEPT ![self] = "addReadTO"]
                                /\ UNCHANGED objLogs
                           ELSE /\ IF req'[self].callType = READ_RESP
                                      THEN /\ pc' = [pc EXCEPT ![self] = "fwdFromTail"]
                                           /\ UNCHANGED objLogs
                                      ELSE /\ IF req'[self].callType = WRITE_INV
                                                 THEN /\ objLogs' = [objLogs EXCEPT ![self][(req'[self].op).obj] = Cons((req'[self].op), @)]
                                                      /\ pc' = [pc EXCEPT ![self] = "propagate"]
                                                 ELSE /\ objLogs' = [objLogs EXCEPT ![self][req'[self].op.obj] = CommitDirtyVersion(@, req'[self].op)]
                                                      /\ pc' = [pc EXCEPT ![self] = "backProp"]
                                /\ UNCHANGED << timeOracle, now >>
                     /\ UNCHANGED << objTotalOrders, allSubmittedWriteOps, 
                                     allSubmittedReadOps, terminatedYet, 
                                     initClient, nonInitClients, start, 
                                     isLinearizable, uninitializedObjs, 
                                     initObj, objs_init, obj_init, 
                                     actions_init, action_init, gateway_cinit, 
                                     msg_cinit, uniqueId_cinit, sentOps_init, 
                                     recvdOps_init, objs, obj, actions, action, 
                                     gateway_c, msg_c, uniqueId, sentOps, 
                                     recvdOps, req_h, sender_h, pendingInvos_h, 
                                     now_h, req_t, sender_t, pendingInvos_t, 
                                     now_t, sender, pendingInvos, submittedOps, 
                                     writes, reads, read, edges, clients, 
                                     match, cli >>

apportionQ(self) == /\ pc[self] = "apportionQ"
                    /\ msgQs' = [msgQs EXCEPT ![<<self, tail>>] = Append(@, req[self])]
                    /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \cup {<<(req[self].uniqueId), sender[self]>>}]
                    /\ pc' = [pc EXCEPT ![self] = "listen"]
                    /\ UNCHANGED << objLogs, objTotalOrders, 
                                    allSubmittedWriteOps, allSubmittedReadOps, 
                                    terminatedYet, initClient, nonInitClients, 
                                    start, timeOracle, isLinearizable, 
                                    uninitializedObjs, initObj, objs_init, 
                                    obj_init, actions_init, action_init, 
                                    gateway_cinit, msg_cinit, uniqueId_cinit, 
                                    sentOps_init, recvdOps_init, objs, obj, 
                                    actions, action, gateway_c, msg_c, 
                                    uniqueId, sentOps, recvdOps, req_h, 
                                    sender_h, pendingInvos_h, now_h, req_t, 
                                    sender_t, pendingInvos_t, now_t, req, 
                                    sender, now, submittedOps, writes, reads, 
                                    read, edges, clients, match, cli >>

addReadTO(self) == /\ pc[self] = "addReadTO"
                   /\ req' = [req EXCEPT ![self] = [callType |-> READ_RESP,
                                                    uniqueId |-> req[self].uniqueId,
                                                    startTs |-> now[self],
                                                    commitTs |-> now[self],
                                                    op |-> Read(self, req[self].op.obj)]]
                   /\ objTotalOrders' = [objTotalOrders EXCEPT ![req'[self].op.obj] = Cons(req'[self], @)]
                   /\ pc' = [pc EXCEPT ![self] = "respFromSelf"]
                   /\ UNCHANGED << msgQs, objLogs, allSubmittedWriteOps, 
                                   allSubmittedReadOps, terminatedYet, 
                                   initClient, nonInitClients, start, 
                                   timeOracle, isLinearizable, 
                                   uninitializedObjs, initObj, objs_init, 
                                   obj_init, actions_init, action_init, 
                                   gateway_cinit, msg_cinit, uniqueId_cinit, 
                                   sentOps_init, recvdOps_init, objs, obj, 
                                   actions, action, gateway_c, msg_c, uniqueId, 
                                   sentOps, recvdOps, req_h, sender_h, 
                                   pendingInvos_h, now_h, req_t, sender_t, 
                                   pendingInvos_t, now_t, sender, now, 
                                   pendingInvos, submittedOps, writes, reads, 
                                   read, edges, clients, match, cli >>

respFromSelf(self) == /\ pc[self] = "respFromSelf"
                      /\ msgQs' = [msgQs EXCEPT ![<<self, sender[self]>>] = Append(@, req[self])]
                      /\ pc' = [pc EXCEPT ![self] = "listen"]
                      /\ UNCHANGED << objLogs, objTotalOrders, 
                                      allSubmittedWriteOps, 
                                      allSubmittedReadOps, terminatedYet, 
                                      initClient, nonInitClients, start, 
                                      timeOracle, isLinearizable, 
                                      uninitializedObjs, initObj, objs_init, 
                                      obj_init, actions_init, action_init, 
                                      gateway_cinit, msg_cinit, uniqueId_cinit, 
                                      sentOps_init, recvdOps_init, objs, obj, 
                                      actions, action, gateway_c, msg_c, 
                                      uniqueId, sentOps, recvdOps, req_h, 
                                      sender_h, pendingInvos_h, now_h, req_t, 
                                      sender_t, pendingInvos_t, now_t, req, 
                                      sender, now, pendingInvos, submittedOps, 
                                      writes, reads, read, edges, clients, 
                                      match, cli >>

fwdFromTail(self) == /\ pc[self] = "fwdFromTail"
                     /\ msgQs' = [msgQs EXCEPT ![<<self, (Find(pendingInvos[self], req[self].uniqueId))>>] = Append(@, req[self])]
                     /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \ {FindPair(pendingInvos[self], (req[self].uniqueId))}]
                     /\ pc' = [pc EXCEPT ![self] = "listen"]
                     /\ UNCHANGED << objLogs, objTotalOrders, 
                                     allSubmittedWriteOps, allSubmittedReadOps, 
                                     terminatedYet, initClient, nonInitClients, 
                                     start, timeOracle, isLinearizable, 
                                     uninitializedObjs, initObj, objs_init, 
                                     obj_init, actions_init, action_init, 
                                     gateway_cinit, msg_cinit, uniqueId_cinit, 
                                     sentOps_init, recvdOps_init, objs, obj, 
                                     actions, action, gateway_c, msg_c, 
                                     uniqueId, sentOps, recvdOps, req_h, 
                                     sender_h, pendingInvos_h, now_h, req_t, 
                                     sender_t, pendingInvos_t, now_t, req, 
                                     sender, now, submittedOps, writes, reads, 
                                     read, edges, clients, match, cli >>

propagate(self) == /\ pc[self] = "propagate"
                   /\ msgQs' = [msgQs EXCEPT ![<<self, (Successors[self])>>] = Append(@, req[self])]
                   /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \cup {<<(req[self].uniqueId), sender[self]>>}]
                   /\ pc' = [pc EXCEPT ![self] = "listen"]
                   /\ UNCHANGED << objLogs, objTotalOrders, 
                                   allSubmittedWriteOps, allSubmittedReadOps, 
                                   terminatedYet, initClient, nonInitClients, 
                                   start, timeOracle, isLinearizable, 
                                   uninitializedObjs, initObj, objs_init, 
                                   obj_init, actions_init, action_init, 
                                   gateway_cinit, msg_cinit, uniqueId_cinit, 
                                   sentOps_init, recvdOps_init, objs, obj, 
                                   actions, action, gateway_c, msg_c, uniqueId, 
                                   sentOps, recvdOps, req_h, sender_h, 
                                   pendingInvos_h, now_h, req_t, sender_t, 
                                   pendingInvos_t, now_t, req, sender, now, 
                                   submittedOps, writes, reads, read, edges, 
                                   clients, match, cli >>

backProp(self) == /\ pc[self] = "backProp"
                  /\ msgQs' = [msgQs EXCEPT ![<<self, (Find(pendingInvos[self], req[self].uniqueId))>>] = Append(@, req[self])]
                  /\ pendingInvos' = [pendingInvos EXCEPT ![self] = pendingInvos[self] \ {FindPair(pendingInvos[self], (req[self].uniqueId))}]
                  /\ pc' = [pc EXCEPT ![self] = "listen"]
                  /\ UNCHANGED << objLogs, objTotalOrders, 
                                  allSubmittedWriteOps, allSubmittedReadOps, 
                                  terminatedYet, initClient, nonInitClients, 
                                  start, timeOracle, isLinearizable, 
                                  uninitializedObjs, initObj, objs_init, 
                                  obj_init, actions_init, action_init, 
                                  gateway_cinit, msg_cinit, uniqueId_cinit, 
                                  sentOps_init, recvdOps_init, objs, obj, 
                                  actions, action, gateway_c, msg_c, uniqueId, 
                                  sentOps, recvdOps, req_h, sender_h, 
                                  pendingInvos_h, now_h, req_t, sender_t, 
                                  pendingInvos_t, now_t, req, sender, now, 
                                  submittedOps, writes, reads, read, edges, 
                                  clients, match, cli >>

n(self) == listen(self) \/ incomingMsg(self) \/ apportionQ(self)
              \/ addReadTO(self) \/ respFromSelf(self) \/ fwdFromTail(self)
              \/ propagate(self) \/ backProp(self)

awaitTermination(self) == /\ pc[self] = "awaitTermination"
                          /\ IF clients[self] /= {}
                                THEN /\ cli' = [cli EXCEPT ![self] = CHOOSE cl \in clients[self] : TRUE]
                                     /\ clients' = [clients EXCEPT ![self] = clients[self] \ {cli'[self]}]
                                     /\ terminatedYet[cli'[self]] = TRUE
                                     /\ pc' = [pc EXCEPT ![self] = "awaitTermination"]
                                     /\ UNCHANGED << writes, reads, edges >>
                                ELSE /\ writes' = [writes EXCEPT ![self] = allSubmittedWriteOps[self]]
                                     /\ edges' = [edges EXCEPT ![self] = {edge \in {<<w1, w2>> : w1, w2 \in writes'[self]}: edge[1].commitTs < edge[2].startTs}]
                                     /\ reads' = [reads EXCEPT ![self] = allSubmittedReadOps[self]]
                                     /\ pc' = [pc EXCEPT ![self] = "addVToG"]
                                     /\ UNCHANGED << clients, cli >>
                          /\ UNCHANGED << msgQs, objLogs, objTotalOrders, 
                                          allSubmittedWriteOps, 
                                          allSubmittedReadOps, terminatedYet, 
                                          initClient, nonInitClients, start, 
                                          timeOracle, isLinearizable, 
                                          uninitializedObjs, initObj, 
                                          objs_init, obj_init, actions_init, 
                                          action_init, gateway_cinit, 
                                          msg_cinit, uniqueId_cinit, 
                                          sentOps_init, recvdOps_init, objs, 
                                          obj, actions, action, gateway_c, 
                                          msg_c, uniqueId, sentOps, recvdOps, 
                                          req_h, sender_h, pendingInvos_h, 
                                          now_h, req_t, sender_t, 
                                          pendingInvos_t, now_t, req, sender, 
                                          now, pendingInvos, submittedOps, 
                                          read, match >>

addVToG(self) == /\ pc[self] = "addVToG"
                 /\ IF reads[self] /= {}
                       THEN /\ read' = [read EXCEPT ![self] = CHOOSE r \in reads[self]: TRUE]
                            /\ reads' = [reads EXCEPT ![self] = reads[self] \ {read'[self]}]
                            /\ edges' = [edges EXCEPT ![self] = edges[self] \cup {<<write, read'[self]>>: write \in {w \in writes[self]: w.commitTs < read'[self].startTs}}]
                            /\ match' = [match EXCEPT ![self] = CHOOSE w \in writes[self]: w.uniqueId = read'[self].op.uniqueId]
                            /\ pc' = [pc EXCEPT ![self] = "merge_read_into_write"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ UNCHANGED << reads, read, edges, match >>
                 /\ UNCHANGED << msgQs, objLogs, objTotalOrders, 
                                 allSubmittedWriteOps, allSubmittedReadOps, 
                                 terminatedYet, initClient, nonInitClients, 
                                 start, timeOracle, isLinearizable, 
                                 uninitializedObjs, initObj, objs_init, 
                                 obj_init, actions_init, action_init, 
                                 gateway_cinit, msg_cinit, uniqueId_cinit, 
                                 sentOps_init, recvdOps_init, objs, obj, 
                                 actions, action, gateway_c, msg_c, uniqueId, 
                                 sentOps, recvdOps, req_h, sender_h, 
                                 pendingInvos_h, now_h, req_t, sender_t, 
                                 pendingInvos_t, now_t, req, sender, now, 
                                 pendingInvos, submittedOps, writes, clients, 
                                 cli >>

merge_read_into_write(self) == /\ pc[self] = "merge_read_into_write"
                               /\ edges' = [edges EXCEPT ![self] = edges[self] \cup { <<write, match[self]>>: write \in {w \in writes[self]: w.commitTs < read[self].startTs}}]
                               /\ pc' = [pc EXCEPT ![self] = "removeSelfEdges"]
                               /\ UNCHANGED << msgQs, objLogs, objTotalOrders, 
                                               allSubmittedWriteOps, 
                                               allSubmittedReadOps, 
                                               terminatedYet, initClient, 
                                               nonInitClients, start, 
                                               timeOracle, isLinearizable, 
                                               uninitializedObjs, initObj, 
                                               objs_init, obj_init, 
                                               actions_init, action_init, 
                                               gateway_cinit, msg_cinit, 
                                               uniqueId_cinit, sentOps_init, 
                                               recvdOps_init, objs, obj, 
                                               actions, action, gateway_c, 
                                               msg_c, uniqueId, sentOps, 
                                               recvdOps, req_h, sender_h, 
                                               pendingInvos_h, now_h, req_t, 
                                               sender_t, pendingInvos_t, now_t, 
                                               req, sender, now, pendingInvos, 
                                               submittedOps, writes, reads, 
                                               read, clients, match, cli >>

removeSelfEdges(self) == /\ pc[self] = "removeSelfEdges"
                         /\ edges' = [edges EXCEPT ![self] = edges[self] \ {e \in edges[self]: e[1] = e[2]}]
                         /\ IF \E e \in edges'[self]: <<e[2], e[1]>> \in edges'[self]
                               THEN /\ isLinearizable' = FALSE
                               ELSE /\ TRUE
                                    /\ UNCHANGED isLinearizable
                         /\ pc' = [pc EXCEPT ![self] = "addVToG"]
                         /\ UNCHANGED << msgQs, objLogs, objTotalOrders, 
                                         allSubmittedWriteOps, 
                                         allSubmittedReadOps, terminatedYet, 
                                         initClient, nonInitClients, start, 
                                         timeOracle, uninitializedObjs, 
                                         initObj, objs_init, obj_init, 
                                         actions_init, action_init, 
                                         gateway_cinit, msg_cinit, 
                                         uniqueId_cinit, sentOps_init, 
                                         recvdOps_init, objs, obj, actions, 
                                         action, gateway_c, msg_c, uniqueId, 
                                         sentOps, recvdOps, req_h, sender_h, 
                                         pendingInvos_h, now_h, req_t, 
                                         sender_t, pendingInvos_t, now_t, req, 
                                         sender, now, pendingInvos, 
                                         submittedOps, writes, reads, read, 
                                         clients, match, cli >>

perObj(self) == awaitTermination(self) \/ addVToG(self)
                   \/ merge_read_into_write(self) \/ removeSelfEdges(self)

Next == iclient \/ he \/ ta
           \/ (\E self \in nonInitClients: c(self))
           \/ (\E self \in Nodes \ {head, tail}: n(self))
           \/ (\E self \in Objects: perObj(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ WF_vars(iclient)
        /\ \A self \in nonInitClients : WF_vars(c(self))
        /\ WF_vars(he)
        /\ WF_vars(ta)
        /\ \A self \in Nodes \ {head, tail} : WF_vars(n(self))
        /\ \A self \in Objects : WF_vars(perObj(self))

\* END TRANSLATION 






GlobalTypeInvariant ==  /\ msgQs \in [Network -> {<< >>} \cup Seq(RequestType)]
                        /\ objLogs \in [Nodes -> [Objects -> {<< >>} \cup Seq(ObjectVersionType)]]
                        /\ objTotalOrders \in [Objects -> Seq(RequestType)]
                        /\ allSubmittedWriteOps \in [Objects -> SUBSET(RequestType)]
                        /\ terminatedYet \in [Clients -> {TRUE, FALSE}]
                        /\ initClient \in Clients
                        /\ nonInitClients = Clients \ {initClient}
                        /\ start \in {TRUE, FALSE}
                        /\ timeOracle \in Nat
                        
                                            
InitClientTypeInvariant ==  /\ \A uninitObj \in uninitializedObjs: uninitObj \in Objects
                            /\ initObj \in Objects
                            /\ \A objInitd \in objs_init: objInitd \in Objects
                            /\ \A inv \in actions_init: inv \in {WRITE_INV, READ_INV}
                            /\ gateway_cinit \in Nodes \cup {NullNode}
                            /\ sentOps_init \in Nat
                            /\ recvdOps_init \in Nat
                            /\ msg_cinit \in RequestType \cup {NullReq}
                            /\ uniqueId_cinit \in UniqueIdType \cup {NullUniqueId}
                            
ClientTypeInvariant ==  \*/\ \A objInited \in objs: objInited \in [Clients -> Objects]
                        /\ obj \in [Clients \ {initClient} -> Objects]
                        /\ actions \in [Clients \ {initClient} -> SUBSET({WRITE_INV, READ_INV})]
                        /\ action \in [Clients \ {initClient} -> {WRITE_INV, READ_INV}]
                        /\ gateway_c \in [Clients \ {initClient} -> Nodes \cup {NullNode}]
                        /\ sentOps \in [Clients \ {initClient} -> Nat]
                        /\ recvdOps \in [Clients \ {initClient} -> Nat]
                        /\ msg_c \in [Clients \ {initClient} -> RequestType \cup {NullReq}]
                        /\ uniqueId \in [Clients \ {initClient} -> UniqueIdType]

\*ClientTypeInvariant ==  /\ uniqueId \in [Clients -> UniqueIdType]
\*                        /\ msg \in [Clients -> RequestType \cup {NullReq}]
\*                        /\ gateway \in [Clients -> Nodes \cup {NullNode}]

                        
NodeTypeInvariant ==    /\ req \in [Nodes \ {head, tail} -> RequestType \cup {NullReq}]
                        /\ sender \in [Nodes \ {head, tail} -> Nodes \cup Clients \cup {NullNode}]
                        /\ now \in [Nodes \ {head, tail} -> Nat]
\*                        /\ pendingInvos \in [Nodes -> thisoneshard
                        
HeadTypeInvariant ==    /\ req_h \in RequestType \cup {NullReq}
                        /\ sender_h \in Nodes \cup Clients \cup {NullNode}
\*                        /\ pendingInvos_h \in thisoneshard
                        /\ now_h \in Nat
                        
TailTypeInvariant ==    /\ req_t \in RequestType \cup {NullReq}
                        /\ sender_t \in Nodes \cup Clients \cup {NullNode}
\*                        /\ pendingInvos_t \in thisoneshard
                        /\ now_t \in Nat
                        
                        
                        
                        
                        
\*
\*RECURSIVE MostRecentWrite(_)
\*MostRecentWrite(totalOrder) == IF totalOrder = << >> THEN NullReq
\*                                ELSE    CASE Head(totalOrder).callType = WRITE_RESP -> Head(totalOrder)
\*                                        [] Head(totalOrder).callType = READ_RESP -> MostRecentWrite(Tail(totalOrder))
\*
\*RECURSIVE ReadPrecededByWrite(_)                                
\*ReadPrecededByWrite(totalOrder) == IF totalOrder = << >> THEN TRUE
\*                                    ELSE LET reqOp == Head(totalOrder)
\*                                             remainder == Tail(totalOrder) IN
\*                                                CASE reqOp.callType = WRITE_RESP -> ReadPrecededByWrite(remainder)
\*                                                [] reqOp.callType = READ_RESP -> LET pastWrite == MostRecentWrite(remainder) IN
\*                                                                                    CASE pastWrite = NullReq -> FALSE
\*                                                                                    [] reqOp.op.uniqueId = pastWrite.op.uniqueId -> 
\*                                                                                        ReadPrecededByWrite(remainder)
\*                                                                                    [] OTHER -> FALSE

                                                                    
\*RealtimeDependency(successor, predecessor) == predecessor.commitTs < successor.startTs
\*IsConcurrent(reqOp1, reqOp2) == ~(  \/ RealtimeDependency(reqOp1, reqOp2)
\*                                    \/ RealtimeDependency(reqOp1, reqOp2))
\*                                                                    
\*RECURSIVE IsConcurrentUntilLessThan(_, _)
\*IsConcurrentUntilLessThan(op, remainder) == IF remainder = << >> THEN TRUE ELSE
\*                                                    LET nextOp == Head(remainder) IN
\*                                                    CASE RealtimeDependency(op, nextOp) -> TRUE
\*                                                    [] IsConcurrent(op, nextOp) -> 
\*                                                        IsConcurrentUntilLessThan(op, Tail(remainder))
\*                                                    [] OTHER -> FALSE
\*                                                 
\*RECURSIVE RespectsRealtime(_)
\*RespectsRealtime(totalOrder) == IF totalOrder = << >> 
\*                                THEN TRUE
\*                                ELSE IF IsConcurrentUntilLessThan(Head(totalOrder), Tail(totalOrder)) 
\*                                        THEN RespectsRealtime(Tail(totalOrder))
\*                                        ELSE FALSE




\*IsLegal(totalOrder) ==  /\ ReadPrecededByWrite(totalOrder)
\*\*                        /\ RespectsRealtime(totalOrder)
\*
\*LegalOrderInvariant == \A o \in Objects: IsLegal(objTotalOrders[o])
\*
\*
\*RECURSIVE ContainsAllOps(_, _)                        
\*ContainsAllOps(totalOrder, setOfOps) == CASE setOfOps = {} -> TRUE
\*                                        [] totalOrder = << >> /\ setOfOps /= {} -> FALSE
\*                                        [] \E reqOp \in setOfOps : reqOp = Head(totalOrder) -> 
\*                                            ContainsAllOps(Tail(totalOrder), setOfOps \ {Head(totalOrder)})
\*                                        [] OTHER -> ContainsAllOps(Tail(totalOrder), setOfOps)  \* newly committed op,
\*                                                                                                \* not yet in total order
\*                                            
\*TotalOrderInvariant == \A o \in Objects: ContainsAllOps(objTotalOrders[o], allSubmittedWriteOps[o])
\*                                            
\*IsTotal(totalOrder, setOfOps) ==    /\ ContainsAllOps(totalOrder, setOfOps)
\*                                    /\ Len(totalOrder) = Cardinality(setOfOps) 
\*                                    
\*
\*IsObjLinearizable(totalOrder, setOfOps) ==  /\ IsLegal(totalOrder)
\*                                            /\ IsTotal(totalOrder, setOfOps) 
                                
Terminated == \A client \in Clients: terminatedYet[client] = TRUE

Linearizability == isLinearizable

=============================================================================
\* Modification History
\* Last modified Fri Jun 23 20:02:52 EDT 2023 by jenniferlam
\* Last modified Sat Jun 17 03:26:39 EDT 2023 by 72jen
\* Created Tue Jun 13 12:56:59 EDT 2023 by jenniferlam
