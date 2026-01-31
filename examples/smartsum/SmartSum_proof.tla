--------------------------- MODULE SmartSum_proof ---------------------------
EXTENDS SmartSum_transf, TLAPS

(* Assume domain of values is integers *)
ASSUMPTION ValDef ==
    Value = Int

(* Arbitrary epsilon (positive real) *)
ASSUMPTION EpsDef ==
    /\ Epsilon \in Real
    /\ Epsilon > 0

(* Arbitrary Q (positive natural) *)
ASSUMPTION QDef ==
    /\ Q \in Nat
    /\ Q # 0

------------------------------------------------------------------------------
(******************************)
(* Type correctness invariant *)
(******************************)

TypeOK == /\ pc \in {"L1", "L2", "Done"}
          /\ l1 \in Seq(Value)
          /\ l2 \in Seq(Value)
          /\ next1 \in Value
          /\ next2 \in Value
          /\ n1 \in Value
          /\ n2 \in Value
          /\ c1 \in Value
          /\ c2 \in Value
          /\ x1 \in Value
          /\ x2 \in Value
          /\ r1 \in Seq(Value)
          /\ r2 \in Seq(Value)
          /\ out1 \in Seq(Value)
          /\ out2 \in Seq(Value)
          /\ /\ v_eps \in Real
             /\ v_eps >= 0
          /\ /\ v_delta \in Real
             /\ v_delta >= 0

THEOREM TypeOKInv == Spec => []TypeOK
  <1>1. Init => TypeOK
    BY ValDef, ZeroIsReal DEF Init, TypeOK
  <1>2. TypeOK /\ [Next]_vars => TypeOK'
    <2> SUFFICES ASSUME TypeOK,
                        [Next]_vars
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. CASE L1
      <3> SUFFICES ASSUME 0 < Len(l1)
                   PROVE  /\ v_eps' \in Real
                          /\ v_eps' >= 0
                          /\ v_delta' \in Real
                          /\ v_delta' >= 0
        <4> USE EpsDef, QDef, ValDef, AbsLapHoareSpecDef, <2>1 DEF L1, TypeOK, AbsLapHoareSpec
        <4>A. l1' \in Seq(Value) OBVIOUS
        <4>B. l2' \in Seq(Value) OBVIOUS
        <4>C. next1' \in Value OBVIOUS
        <4>D. next2' \in Value OBVIOUS
        <4>E. n1' \in Value OBVIOUS
        <4>F. n2' \in Value OBVIOUS
        <4>G. c1' \in Value OBVIOUS
        <4>H. c2' \in Value OBVIOUS
        <4>I. x1' \in Value OBVIOUS
        <4>J. x2' \in Value OBVIOUS
        <4>K. out1' \in Seq(Value) OBVIOUS
        <4>L. out2' \in Seq(Value) OBVIOUS
        <4> HIDE EpsDef, QDef
        <4>M. r1' \in Seq(Value) OBVIOUS
        <4>N. r2' \in Seq(Value) OBVIOUS
        <4> QED
          BY <4>A, <4>B, <4>C, <4>D, <4>E, <4>F, <4>G, <4>H, <4>I, <4>J, <4>K, <4>L
      <3>1. CASE Len(l1) % Q = 0
        \* <4>1. v_eps' = v_eps + Epsilon * AbsVal(c1 + Head(l1) - (c2 + Head(l2)))
        \*   BY <2>1, <3>1, AbsLapHoareSpecDef DEF L1, TypeOK, AbsLapHoareSpec
        \* <4>2. v_delta' = v_delta
        \*   BY <2>1, AbsLapHoareSpecDef DEF L1, TypeOK, AbsLapHoareSpec
        \* <4> QED
      <3>2. CASE Len(l1) % Q # 0
      <3> QED
        BY <3>1, <3>2
    <2>2. CASE L2
      BY <2>2 DEF L2, TypeOK
    <2>3. CASE Terminating
      BY <2>3 DEF Terminating, vars, TypeOK
    <2>4. CASE UNCHANGED vars
      BY <2>4 DEF vars, TypeOK
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4 DEF Next
  <1> QED
    BY <1>1, <1>2, PTL DEF Spec

=============================================================================
