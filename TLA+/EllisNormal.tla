----------------------------- MODULE EllisNormal -----------------------------
EXTENDS Naturals, FiniteSets, Sequences, IOCLSpec

CONSTANTS Ops, Clients, Shards, Keys,
          client, shard, key

ASSUME /\ client \in [Ops -> Clients]
       /\ shard  \in [Ops -> Shards]
       /\ key    \in [Ops -> Keys]

VARIABLES
    phase,
    firstDurable,
    arrivalTS,
    finalTS,
    nextTS,
    initSeen,
    finalSeen,
    commitLog,
    executed,

    invocationOrder,
    realTimeOrder,
    shardOrder,
    predRel,
    returned,
    failed

vars ==
    << phase, firstDurable, arrivalTS, finalTS, nextTS,
       initSeen, finalSeen, commitLog, executed,
       invocationOrder, realTimeOrder, shardOrder,
       predRel, returned, failed >>

NotInvoked == "NotInvoked"
Pending    == "Pending"
Initial    == "Initial"
Final      == "Final"
Ordered    == "Ordered"
Executed   == "Executed"
Returned   == "Returned"

Invoked ==
    {o \in Ops : phase[o] # NotInvoked}

Outstanding(c) ==
    {o \in Invoked :
        /\ client[o] = c
        /\ o \notin returned
        /\ o \notin failed}

Preds(o) ==
    {p \in Ops : <<p,o>> \in predRel}

PriorClientOps(o) ==
    {p \in Invoked : client[p] = client[o]}

SetMax(S) ==
    CHOOSE m \in S : \A x \in S : x <= m

CurrentTS(o) ==
    IF phase[o] \in {Final, Ordered, Executed, Returned}
    THEN finalTS[o]
    ELSE arrivalTS[o]

SameKeyPending(o) ==
    {p \in Ops :
        /\ p # o
        /\ key[p] = key[o]
        /\ shard[p] = shard[o]
        /\ phase[p] \in {Initial, Final}}

AtPerKeyHead(o) ==
    \A p \in SameKeyPending(o) :
        CurrentTS(o) < CurrentTS(p)

AllInitSeen(o) ==
    \A p \in Preds(o) : <<p,o>> \in initSeen

AllFinalSeen(o) ==
    \A p \in Preds(o) : <<p,o>> \in finalSeen

EarlierInLog(o) ==
    {p \in Ops :
        \E i,j \in DOMAIN commitLog[shard[o]] :
            /\ i < j
            /\ commitLog[shard[o]][i] = p
            /\ commitLog[shard[o]][j] = o}

Init ==
    /\ phase = [o \in Ops |-> NotInvoked]
    /\ firstDurable = {}
    /\ arrivalTS = [o \in Ops |-> 0]
    /\ finalTS = [o \in Ops |-> 0]
    /\ nextTS = [s \in Shards |-> 1]
    /\ initSeen = {}
    /\ finalSeen = {}
    /\ commitLog = [s \in Shards |-> <<>>]
    /\ executed = {}
    /\ invocationOrder = {}
    /\ realTimeOrder = {}
    /\ shardOrder = {}
    /\ predRel = {}
    /\ returned = {}
    /\ failed = {}

Invoke(o) ==
    /\ phase[o] = NotInvoked
    /\ LET prior == PriorClientOps(o)
           outstanding == Outstanding(client[o])
       IN /\ invocationOrder' =
                 invocationOrder \cup {<<p,o>> : p \in prior}
          /\ predRel' =
                 predRel \cup {<<p,o>> : p \in outstanding}
          /\ realTimeOrder' =
                 realTimeOrder \cup {<<p,o>> : p \in returned}
    /\ phase' = [phase EXCEPT ![o] = Pending]
    /\ UNCHANGED << firstDurable, arrivalTS, finalTS, nextTS,
                    initSeen, finalSeen, commitLog, executed,
                    shardOrder, returned, failed >>

(* First VR round, abstracted as one durable transition. *)
FirstReplicate(o) ==
    /\ phase[o] = Pending
    /\ phase' = [phase EXCEPT ![o] = Initial]
    /\ firstDurable' = firstDurable \cup {o}
    /\ arrivalTS' = [arrivalTS EXCEPT ![o] = nextTS[shard[o]]]
    /\ nextTS' = [nextTS EXCEPT ![shard[o]] = @ + 1]
    /\ UNCHANGED << finalTS, initSeen, finalSeen, commitLog, executed,
                    invocationOrder, realTimeOrder, shardOrder,
                    predRel, returned, failed >>

(* Initial ordering information can be exposed only after round 1 is durable. *)
InitialCoordReply(p,o) ==
    /\ <<p,o>> \in predRel
    /\ p \in firstDurable
    /\ <<p,o>> \notin initSeen
    /\ initSeen' = initSeen \cup {<<p,o>>}
    /\ UNCHANGED << phase, firstDurable, arrivalTS, finalTS, nextTS,
                    finalSeen, commitLog, executed,
                    invocationOrder, realTimeOrder, shardOrder,
                    predRel, returned, failed >>

(*
  Version-0 abstraction of Ellis's timestamp calculation.
  We will replace this with the exact recursive rule once the model shell
  runs and we start testing the real invariants.
*)
Finalize(o) ==
    /\ phase[o] = Initial
    /\ AllInitSeen(o)
    /\ LET bound ==
          IF Preds(o) = {}
          THEN arrivalTS[o]
          ELSE SetMax({arrivalTS[o]} \cup
                      {arrivalTS[p] + 1 : p \in Preds(o)})
       IN finalTS' = [finalTS EXCEPT ![o] = bound]
    /\ phase' = [phase EXCEPT ![o] = Final]
    /\ UNCHANGED << firstDurable, arrivalTS, nextTS,
                    initSeen, finalSeen, commitLog, executed,
                    invocationOrder, realTimeOrder, shardOrder,
                    predRel, returned, failed >>

(* Per-key HOL before entering the ordered commit log. *)
SecondReplicate(o) ==
    /\ phase[o] = Final
    /\ AtPerKeyHead(o)
    /\ phase' = [phase EXCEPT ![o] = Ordered]
    /\ commitLog' =
         [commitLog EXCEPT ![shard[o]] = Append(@, o)]
    /\ UNCHANGED << firstDurable, arrivalTS, finalTS, nextTS,
                    initSeen, finalSeen, executed,
                    invocationOrder, realTimeOrder, shardOrder,
                    predRel, returned, failed >>

FinalCoordReply(p,o) ==
    /\ <<p,o>> \in predRel
    /\ phase[p] \in {Final, Ordered, Executed, Returned}
    /\ <<p,o>> \notin finalSeen
    /\ finalSeen' = finalSeen \cup {<<p,o>>}
    /\ UNCHANGED << phase, firstDurable, arrivalTS, finalTS, nextTS,
                    initSeen, commitLog, executed,
                    invocationOrder, realTimeOrder, shardOrder,
                    predRel, returned, failed >>

Execute(o) ==
    /\ phase[o] = Ordered
    /\ AllFinalSeen(o)
    /\ EarlierInLog(o) \subseteq executed
    /\ LET priorExecuted == {p \in executed : shard[p] = shard[o]}
       IN shardOrder' =
             shardOrder \cup {<<p,o>> : p \in priorExecuted}
    /\ executed' = executed \cup {o}
    /\ phase' = [phase EXCEPT ![o] = Executed]
    /\ UNCHANGED << firstDurable, arrivalTS, finalTS, nextTS,
                    initSeen, finalSeen, commitLog,
                    invocationOrder, realTimeOrder, predRel,
                    returned, failed >>

Return(o) ==
    /\ phase[o] = Executed
    /\ phase' = [phase EXCEPT ![o] = Returned]
    /\ returned' = returned \cup {o}
    /\ UNCHANGED << firstDurable, arrivalTS, finalTS, nextTS,
                    initSeen, finalSeen, commitLog, executed,
                    invocationOrder, realTimeOrder, shardOrder,
                    predRel, failed >>

Next ==
    \/ \E o \in Ops : Invoke(o)
    \/ \E o \in Ops : FirstReplicate(o)
    \/ \E p,o \in Ops : InitialCoordReply(p,o)
    \/ \E o \in Ops : Finalize(o)
    \/ \E o \in Ops : SecondReplicate(o)
    \/ \E p,o \in Ops : FinalCoordReply(p,o)
    \/ \E o \in Ops : Execute(o)
    \/ \E o \in Ops : Return(o)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ phase \in [Ops ->
          {NotInvoked, Pending, Initial, Final, Ordered, Executed, Returned}]
    /\ firstDurable \subseteq Ops
    /\ executed \subseteq Ops
    /\ returned \subseteq Ops
    /\ failed \subseteq Ops
    /\ invocationOrder \subseteq Ops \X Ops
    /\ realTimeOrder \subseteq Ops \X Ops
    /\ shardOrder \subseteq Ops \X Ops
    /\ predRel \subseteq Ops \X Ops
    /\ initSeen \subseteq Ops \X Ops
    /\ finalSeen \subseteq Ops \X Ops

InvCoordAfterDurable ==
    \A e \in initSeen : e[1] \in firstDurable

InvPredIsInvocationOrder ==
    predRel \subseteq invocationOrder

InvReturnedExecuted ==
    returned \subseteq executed

InvFinalSeenMeansFinal ==
    \A e \in finalSeen :
        phase[e[1]] \in {Final, Ordered, Executed, Returned}

=============================================================================
