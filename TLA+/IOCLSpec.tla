------------------------------ MODULE IOCLSpec ------------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT Ops

(*declaring state variables*)
VARIABLES
    invocationOrder,
    realTimeOrder,
    shardOrder,
    predRel,
    returned,
    failed

(*vars is a sequence containing all 6 variables*)
vars == << invocationOrder, realTimeOrder, shardOrder,
          predRel, returned, failed >>

(*s is a sequence. in TLA+, a sequence is really just a function whos domain is 1..n and the value of the function is the elem in the sequence. *)
BeforeInSeq(a,b,s) ==
    \E i,j \in DOMAIN s :
        /\ i < j
        /\ s[i] = a
        /\ s[j] = b

NoDuplicates(s) ==
    \A i,j \in DOMAIN s :
        i # j => s[i] # s[j]

Elems(s) == {s[i] : i \in DOMAIN s} (*creates a set from a sequence, discards duplicates*)

(*s is a sequence, S is a set. TLA+ sets are unordered*)
IsPermutationOf(s,S) ==
    /\ NoDuplicates(s)
    /\ Elems(s) = S
    /\ Len(s) = Cardinality(S)


(*R is a relation - set of ordered pairs. R expresses ordering constraints
ex) R = {
    <<"A", "B">>,
    <<"A", "C">>,
    <<"C", "D">>
}
could be
A<B, A<C, C<D

s = <<A,C,B>> THIS EXTENDS R
s = <<A,B,C>> THIS ALSO EXTENDS R
s = <<C,A<B>> THIS DOES NOT EXTENDS R
*)
Extends(s,R) == (*s is a linearization of R???*)
    (*for all ordered pairs o_p in the relation R...*)
    \A o_p \in R :
        (*if both elements are in the sequence/if the whole ordered pair is in the sequence*)
        /\ o_p[1] \in Elems(s)
        /\ o_p[2] \in Elems(s)
        (*those elements must appear in order in the sequence*)
        => BeforeInSeq(o_p[1], o_p[2], s)
(*so to be an extension, (1) the sequence has to have a subset of all the elements in R, 
                         (2) all "whole" ordered pairs have to appear in order in the sequence
                         (3) any ordering across ordered pairs that don't have an order in the relation is valid (ie, B and C)*)

(*All ordered pairs in relation R that that contain ONLY operations that have successfully completed and returned to the client*)
SuccessfulEdges(R) ==
    { e \in R :
        /\ e[1] \in returned
        /\ e[2] \in returned }

(*
  Abstraction boundary for !!!!!VERSION 0!!!!!:
  shardOrder records the actual sequential order in which a shard executes
  operations. Extending it therefore preserves the per-object semantics of
  the shard's sequential execution.

  Later, if we model concrete reads/writes/return values, this predicate can
  be replaced by an explicit sequential-specification legality check.
*)
LegalPerObject(s) ==
    (*Given that a shard contains an execution log and that we can make a Relation from that execution log...*)
    (*some sequence s represents a Legal order on object s if and only iff:
                the "successfully completed shard operations that have executed and returned to clients"  *)
    Extends(s, SuccessfulEdges(shardOrder))
    (*Note: we're assuming the sequential execution performed at a shard is legal for the underlying object, without modeling the actual KV values/reads/writes/return values.*)

(* A sequence containing every successful operation. *)
(*In TLA+, [S->T] means "the set of all functions from S to T"*)
(*So this expression is returning the set of all functions whos domain is 
  {1,2,3,...#returned_ops} and whos values are returned ops.
   --> Given the defn of a sequence being a function, you can think of these functions as sequences.

- for 3 successfully returned ops, there's 3^3 possible functions/sequences.*)
CandidateLinearizations ==
    [1..Cardinality(returned) -> returned] (*All possible N-length sequences with elems in returned*)

(*1*)
IOCLOrdering ==
    \E lin \in CandidateLinearizations : (*All possible N-length sequences with elems in returned*)
        /\ IsPermutationOf(lin, returned) (*throws away duplicates*)
        /\ LegalPerObject(lin) (*respects shard order*)
        /\ Extends(lin, SuccessfulEdges(invocationOrder)) (*respects invocation order*)
        /\ Extends(lin, SuccessfulEdges(realTimeOrder)) (*respects real time*)

(*
  It is enough to require this for predecessor edges. Repeated application
  gives the same property for transitive predecessors.
*)
(*2*)
SuffixClosedFailures ==
    \A e \in predRel :
        e[2] \in returned => e[1] \in returned

(* Top-level theorem/specification: 𝒯 *)
(* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
T == IOCLOrdering /\ SuffixClosedFailures

=============================================================================
