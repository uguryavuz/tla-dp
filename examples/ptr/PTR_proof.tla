----------------------------- MODULE PTR_proof -------------------------------
EXTENDS PTR_transf, FiniteSets, TLAPS

(* Arbitrary epsilon (positive integer) *)
ASSUMPTION EpsNat == Epsilon \in Nat

(* Types of constants *)
ASSUMPTION DistType == Dist \in [DBDomain \X DBDomain -> Nat]
ASSUMPTION QueryType == Query \in [DBDomain -> QOutDomain]
ASSUMPTION DummyQOutType == DummyQOut \in QOutDomain

LEMMA MaxElement ==
    ASSUME NEW S, IsFiniteSet(S), S \in SUBSET Int, S # {}
    PROVE  \E x \in S : (\A y \in S : y <= x)

------------------------------------------------------------------------------
(* Type correctness invariant *)

TypeOK == /\ pc \in {"L1", "L2", "L3", "Done"}
          /\ d1 \in DBDomain
          /\ d2 \in DBDomain
          /\ x1 \in Nat
          /\ x2 \in Nat
          /\ y1 \in Int
          /\ y2 \in Int
          /\ out1 \in QOutDomain
          /\ out2 \in QOutDomain
          /\ v_eps \in Nat
          /\ v_delta \in Nat

ASSUMPTION DTIWellDefined == DTI(Query, d1) \in Nat /\ DTI(Query, d2) \in Nat

THEOREM TypeOKInv == Spec => []TypeOK
  <1>1. Init => TypeOK
    BY DEF Init, TypeOK
  <1>2. TypeOK /\ [Next]_vars => TypeOK'
    <2> USE EpsNat, DistType, QueryType, DummyQOutType
    <2>1. CASE L1
      <3> SUFFICES DTI(Query, d1) \in Nat /\ DTI(Query, d2) \in Nat
        BY <2>1 DEF L1, TypeOK
    \*   <3> DEFINE dists1 == {x \in Nat : \A d_pr \in DBDomain : Dist[d1, d_pr] <= x => Query[d_pr] = Query[d1]}
    \*   <3> DEFINE dists2 == {x \in Nat : \A d_pr \in DBDomain : Dist[d2, d_pr] <= x => Query[d_pr] = Query[d2]}
    \*   <3>1. DTI(Query, d1) = Max(dists1) /\ DTI(Query, d2) = Max(dists2)
    \*     BY Zenon DEF DTI
    \*   <3>2. dists1 \in SUBSET Nat /\ dists2 \in SUBSET Nat
    \*     BY DEF dists1, dists2
    \*   \* <3> SUFFICES /\ \E x \in Nat : \A d_pr \in DBDomain : Dist[d1, d_pr] <= x => Query[d_pr] = Query[d1]
    \*   \*              /\ \E x \in Nat : \A d_pr \in DBDomain : Dist[d2, d_pr] <= x => Query[d_pr] = Query[d2]
    \*   \*   BY <3>1, Zenon DEF Max
      <3> QED
    <2>2. CASE L2
    <2>3. CASE L3
    <2>4. CASE Terminating
    <2>5. CASE UNCHANGED vars
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
  <1> QED
    BY <1>1, <1>2, PTL DEF Spec

==============================================================================