--------------------------- MODULE 2xLaplace_proof ---------------------------
EXTENDS 2xLaplace_transf, TLAPS

(* Assume domain of values is reals *)
(***************************************************************************)
(* Note: Why we do not instantiate 2xLaplace_transf with Value <- Int,     *)
(* and instead extend the module and add this assumption is because        *)
(* we would otherwise need to declare the variables, and all the constants *)
(* incl. those that are to be left opaque (bsLap, Lap, AbsExp and Exp)     *)
(* which creates unnecessary clutter.                                      *)
(***************************************************************************)

ASSUMPTION ValDef == 
  Value = Int

(* Arbitrary epsilon (positive real) *)
ASSUMPTION EpsDef == 
  /\ Epsilon \in Real
  /\ Epsilon > 0

------------------------------------------------------------------------------
(******************************)
(* Type correctness invariant *)
(******************************)

TypeOK == /\ pc \in {"L1", "L2", "L3", "Done"}
          /\ mem1 \in [a: Value, b: Value]
          /\ mem2 \in [a: Value, b: Value]
          /\ y1 \in Value
          /\ y2 \in Value
          /\ z1 \in Value
          /\ z2 \in Value
          /\ out1 \in Value \X Value
          /\ out2 \in Value \X Value
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
      <3> SUFFICES v_eps' \in Real /\ v_eps' >= 0
        BY <2>1, EpsDef, AbsLapHoareSpecDef DEF L1, TypeOK, AbsLapHoareSpec
      <3>1. v_eps' = v_eps + Epsilon * AbsVal(mem1.a - mem2.a)
        BY <2>1, EpsDef, AbsLapHoareSpecDef DEF L1, TypeOK, AbsLapHoareSpec
      <3>2. v_eps \in Real /\ v_eps >= 0
        BY DEF TypeOK
      <3>3. Epsilon \in Real /\ Epsilon > 0
        BY EpsDef
      <3>4. mem1.a \in Value /\ mem2.a \in Value
        BY DEF TypeOK
      <3> QED
        \* BY <3>1, <3>2, <3>3, <3>4, ValDef DEF AbsVal
        \* omitted due to lack of real arithmetic support
        OMITTED
    <2>2. CASE L2
      <3> SUFFICES v_eps' \in Real /\ v_eps' >= 0
        BY <2>2, EpsDef, AbsLapHoareSpecDef DEF L2, TypeOK, AbsLapHoareSpec
      <3>1. v_eps' = v_eps + Epsilon * AbsVal(mem1.b - mem2.b)
        BY <2>2, EpsDef, AbsLapHoareSpecDef DEF L2, TypeOK, AbsLapHoareSpec
      <3>2. v_eps \in Real /\ v_eps >= 0
        BY DEF TypeOK
      <3>3. Epsilon \in Real /\ Epsilon > 0
        BY EpsDef
      <3>4. mem1.b \in Value /\ mem2.b \in Value
        BY DEF TypeOK
      <3> QED
        \* BY <3>1, <3>2, <3>3, <3>4, ValDef DEF AbsVal
        \* omitted due to lack of real arithmetic support
        OMITTED
    <2>3. CASE L3
      BY <2>3 DEF L3, TypeOK
    <2>4. CASE Terminating
      BY <2>4 DEF Terminating, vars, TypeOK
    <2>5. CASE UNCHANGED vars
      BY <2>5 DEF vars, TypeOK
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
  <1> QED
    BY <1>1, <1>2, PTL DEF Spec

------------------------------------------------------------------------------
(***************************************************************************)
(* Defining notion of adjacency between initial memories, and proving that *)
(* this relation is conserved by the program.                              *)
(***************************************************************************)

Phi(m1, m2) ==
  /\ AbsVal(m1.a - m2.a) <= 1
  /\ AbsVal(m1.b - m2.b) <= 1

PhiSpec ==
  /\ Spec
  /\ Phi(mem1, mem2)

THEOREM PhiInv == PhiSpec => []Phi(mem1, mem2)
  <1> SUFFICES ASSUME Phi(mem1, mem2), [Next]_vars 
               PROVE Phi(mem1, mem2)'
    BY PTL DEF PhiSpec, Spec
  <1>1. Phi(mem1, mem2) /\ L1 => Phi(mem1, mem2)'
    BY DEF L1, Phi
  <1>2. Phi(mem1, mem2) /\ L2 => Phi(mem1, mem2)'
    BY DEF L2, Phi
  <1>3. Phi(mem1, mem2) /\ L3 => Phi(mem1, mem2)'
    BY DEF L3, Phi
  <1>4. Phi(mem1, mem2) /\ Terminating => Phi(mem1, mem2)'
    BY DEF Terminating, vars, Phi
  <1>5. Phi(mem1, mem2) /\ UNCHANGED vars => Phi(mem1, mem2)'
    BY DEF vars, Phi
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next

------------------------------------------------------------------------------
(***********************)
(* Inductive invariant *)
(***********************)

IInv == 
  /\ pc = "L1"   => (v_eps = 0 /\ v_delta = 0)
  /\ pc = "L2"   => (v_eps <= Epsilon /\ y1 = y2 /\ v_delta = 0)
  /\ pc = "L3"   => (v_eps <= 2 * Epsilon /\ y1 = y2 /\ z1 = z2 /\ v_delta = 0)
  /\ pc = "Done" => (v_eps <= 2 * Epsilon /\ out1 = out2 /\ v_delta = 0)

THEOREM IndInv == PhiSpec => []IInv
  <1> SUFFICES ASSUME []TypeOK,
                      []Phi(mem1, mem2)
               PROVE  Spec => []IInv
    BY TypeOKInv, PhiInv, PTL DEF PhiSpec
  <1>1. Init => IInv
    BY DEF Init, IInv
  <1>2. IInv /\ [Next]_vars => IInv'
    <2> SUFFICES ASSUME IInv,
                        [Next]_vars
                 PROVE  IInv'
      OBVIOUS
    <2>1. CASE L1
      <3> SUFFICES v_eps' <= Epsilon /\ y1' = y2' /\ v_delta' = 0
        BY <2>1 DEF L1, IInv
      <3>0. Phi(mem1, mem2) /\ TypeOK
        BY PTL
      <3>1. /\ v_eps' = v_eps + Epsilon * AbsVal(mem1.a - mem2.a)
            /\ v_delta' = v_delta
            /\ y1' = y2'
        BY <2>1, <3>0, EpsDef, AbsLapHoareSpecDef DEF L1, TypeOK, AbsLapHoareSpec
      <3>2. v_eps = 0 /\ v_delta = 0
        BY <2>1 DEF L1, IInv
      <3> SUFFICES 0 + Epsilon * AbsVal(mem1.a - mem2.a) <= Epsilon
        BY <3>1, <3>2
      <3>3. Epsilon \in Real /\ Epsilon > 0
        BY EpsDef
      <3>4. mem1.a \in Value /\ mem2.a \in Value
        BY <3>0 DEF TypeOK
      <3> QED
        \* BY <3>3, <3>4, ValDef DEF AbsVal
        \* omitted due to lack of real arithmetic support
        OMITTED
    <2>2. CASE L2
      <3> SUFFICES v_eps' <= 2 * Epsilon /\ z1' = z2' /\ v_delta' = 0
        BY <2>2 DEF L2, IInv
      <3>0. Phi(mem1, mem2) /\ TypeOK
        BY PTL
      <3>1. /\ v_eps' = v_eps + Epsilon * AbsVal(mem1.b - mem2.b)
            /\ v_delta' = v_delta
            /\ z1' = z2'
        BY <2>2, <3>0, EpsDef, AbsLapHoareSpecDef DEF L2, TypeOK, AbsLapHoareSpec
      <3>2. v_delta = 0
        BY <2>2 DEF L2, IInv
      <3> SUFFICES v_eps + Epsilon * AbsVal(mem1.b - mem2.b) <= 2 * Epsilon
        BY <3>1, <3>2
      <3>3. Epsilon \in Real /\ Epsilon > 0
        BY EpsDef
      <3>4. 0 <= v_eps /\ v_eps <= Epsilon
        BY <2>2, <3>0 DEF L2, IInv, TypeOK
      <3>5. mem1.b \in Value /\ mem2.b \in Value
        BY <3>0 DEF TypeOK
      <3> QED
        \* BY <3>0 DEF AbsVal, Phi, TypeOK, ValDef
        \* omitted due to lack of real arithmetic support
        OMITTED
    <2>3. CASE L3
      BY <2>3 DEF L3, IInv
    <2>4. CASE Terminating
      BY <2>4 DEF Terminating, vars, IInv
    <2>5. CASE UNCHANGED vars
      BY <2>5 DEF vars, IInv
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
  <1> QED
    BY <1>1, <1>2, PTL DEF Spec

------------------------------------------------------------------------------
(******************************************)
(* Proof of (2 * Epsilon, 0)-DP w.r.t Phi *)
(******************************************)

(***********************)
(* (2 * Epsilon, 0)-DP *)
(***********************)
DP ==
  pc = "Done" =>
    /\ out1 = out2
    /\ v_delta = 0
    /\ v_eps <= 2 * Epsilon

THEOREM DPTheorem == PhiSpec => []DP
  BY IndInv, PTL DEF IInv, DP

==============================================================================
