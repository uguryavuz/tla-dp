--------------------------- MODULE 2xLaplace_proof ---------------------------
EXTENDS 2xLaplace_transf, TLAPS

(* Arbitrary epsilon (positive integer) *)
ASSUMPTION EpsNat == Epsilon \in Nat

------------------------------------------------------------------------------
(* Type correctness invariant *)

TypeOK == /\ pc \in {"L1", "L2", "L3", "Done"}
          /\ mem1 \in [a: Int, b: Int]
          /\ mem2 \in [a: Int, b: Int]
          /\ y1 \in Int
          /\ y2 \in Int
          /\ z1 \in Int
          /\ z2 \in Int
          /\ out1 \in Int \X Int
          /\ out2 \in Int \X Int
          /\ v_eps \in Nat
          /\ v_delta \in Nat

THEOREM TypeOKInv == Spec => []TypeOK
  <1>1. Init => TypeOK
    BY DEF Init, TypeOK
  <1>2. TypeOK /\ [Next]_vars => TypeOK'
    <2> USE EpsNat
    <2> SUFFICES ASSUME TypeOK,
                        [Next]_vars
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. CASE L1
      <3> SUFFICES /\ v_eps' \in Int
                   /\ v_eps' >= 0
                   /\ v_delta' \in Int
                   /\ v_delta' >= 0
        BY <2>1, AbsLapHoareSpecForInts DEF L1, TypeOK
      <3>1. v_eps' = v_eps + Epsilon * AbsVal(mem1.a - mem2.a)
        BY <2>1, AbsLapHoareSpecForInts DEF L1, TypeOK
      <3>2. v_delta' = v_delta
        BY <2>1, AbsLapHoareSpecForInts DEF L1, TypeOK
      <3> SUFFICES AbsVal(mem1.a - mem2.a) \in Int /\ AbsVal(mem1.a - mem2.a) >= 0
        BY <3>1, <3>2 DEF TypeOK
      <3> QED
        BY DEF AbsVal, TypeOK
    <2>2. CASE L2
      <3> SUFFICES /\ v_eps' \in Int
                   /\ v_eps' >= 0
                   /\ v_delta' \in Int
                   /\ v_delta' >= 0
        BY <2>2, AbsLapHoareSpecForInts DEF L2, TypeOK
      <3>1. v_eps' = v_eps + Epsilon * AbsVal(mem1.b - mem2.b)
        BY <2>2, AbsLapHoareSpecForInts DEF L2, TypeOK
      <3>2. v_delta' = v_delta
        BY <2>2, AbsLapHoareSpecForInts DEF L2, TypeOK
      <3> SUFFICES AbsVal(mem1.b - mem2.b) \in Int /\ AbsVal(mem1.b - mem2.b) >= 0
        BY <3>1, <3>2 DEF TypeOK
      <3> QED
        BY DEF AbsVal, TypeOK
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
(* Initial relation between memories *)

Phi(m1, m2) == 
  /\ AbsVal(m1.a - m2.a) <= 1
  /\ AbsVal(m1.b - m2.b) <= 1

THEOREM PhiInv == Phi(mem1, mem2) /\ Spec => []Phi(mem1, mem2)
  <1> SUFFICES ASSUME Phi(mem1, mem2), [Next]_vars 
               PROVE Phi(mem1, mem2)'
    BY PTL DEF Spec
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
(* Inductive invariant *)

IInv == 
  /\ pc = "L1"   => (v_eps = 0 /\ v_delta = 0)
  /\ pc = "L2"   => (v_eps <= Epsilon /\ y1 = y2 /\ v_delta = 0)
  /\ pc = "L3"   => (v_eps <= 2 * Epsilon /\ y1 = y2 /\ z1 = z2 /\ v_delta = 0)
  /\ pc = "Done" => (v_eps <= 2 * Epsilon /\ out1 = out2 /\ v_delta = 0)

THEOREM IndInv == Phi(mem1, mem2) /\ Spec => []IInv
  <1> SUFFICES ASSUME []TypeOK,
                      []Phi(mem1, mem2)
               PROVE  Spec => []IInv
    BY TypeOKInv, PhiInv, PTL
  <1>1. Init => IInv
    BY DEF Init, IInv
  <1>2. IInv /\ [Next]_vars => IInv'
    <2> USE EpsNat
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
        BY <2>1, <3>0, AbsLapHoareSpecForInts DEF L1, TypeOK
      <3>2. v_eps = 0 /\ v_delta = 0
        BY <2>1 DEF L1, IInv
      <3> SUFFICES AbsVal(mem1.a - mem2.a) \in 0..1
        BY <3>1, <3>2, <3>0 DEF TypeOK
      <3> QED
        BY <3>0 DEF AbsVal, Phi, TypeOK
    <2>2. CASE L2
      <3> SUFFICES v_eps' <= 2 * Epsilon /\ z1' = z2' /\ v_delta' = 0
        BY <2>2 DEF L2, IInv
      <3>0. Phi(mem1, mem2) /\ TypeOK
        BY PTL
      <3>1. /\ v_eps' = v_eps + Epsilon * AbsVal(mem1.b - mem2.b)
            /\ v_delta' = v_delta
            /\ z1' = z2'
        BY <2>2, <3>0, AbsLapHoareSpecForInts DEF L2, TypeOK
      <3>2. v_eps <= Epsilon /\ v_delta = 0
        BY <2>2 DEF L2, IInv
      <3> SUFFICES AbsVal(mem1.b - mem2.b) \in 0..1
        BY <3>1, <3>2, <3>0 DEF TypeOK
      <3> QED
        BY <3>0 DEF AbsVal, Phi, TypeOK
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
(* Proof of (2 * Epsilon, 0)-DP w.r.t Phi *)

THEOREM DP == 
  Phi(mem1, mem2) /\ Spec 
    => [](pc = "Done" => /\ out1 = out2
                         /\ v_delta = 0
                         /\ v_eps <= 2 * Epsilon)
  BY IndInv, PTL DEF IInv

==============================================================================