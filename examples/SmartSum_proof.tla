--------------------------- MODULE SmartSum_proof ---------------------------
EXTENDS Integers, DP_Specs, TLAPS

(* To instantiate properly *)
-----------------------------------------------------------------------------
CONSTANTS Lap(_, _), Exp(_, _, _), AbsExp(_, _, _, _, _, _, _) (* left as consts *)
VARIABLES pc, l1, l2, next1, next2, n1, n2, c1, c2, x1, x2, r1, r2, out1, 
          out2, v_eps, v_delta
-----------------------------------------------------------------------------

(* Arbitrary epsilon (positive integer) *)
EpsDef == CHOOSE eps \in Int : eps >= 0

(* Arbitrary Q (strictly positive, integer) *)
Q == CHOOSE q \in Int : 0 < q

(* Instantiate transformed 2xLaplace with EpsDef, Hoare spec of AbsLap *)
INSTANCE SmartSum_transf
  WITH 
    Eps <- EpsDef,
    AbsLap <- AbsLapSpec

-----------------------------------------------------------------------------
(* Type correctness invariant *)

TypeOK == /\ pc \in {"L1", "L2", "Done"}
          /\ l1 \in Seq(Int)
          /\ l2 \in Seq(Int)
          /\ next1 \in Int
          /\ next2 \in Int
          /\ n1 \in Int
          /\ n2 \in Int
          /\ c1 \in Int
          /\ c2 \in Int
          /\ x1 \in Int
          /\ x2 \in Int
          /\ r1 \in Seq(Int)
          /\ r2 \in Seq(Int)
          /\ out1 \in Seq(Int)
          /\ out2 \in Seq(Int)
          /\ /\ v_eps \in Int
             /\ v_eps >= 0
          /\ /\ v_delta \in Int
             /\ v_delta >= 0

THEOREM TypeOKInv == Spec => []TypeOK
  <1>1. Init => TypeOK
    BY DEF Init, TypeOK
  <1>2. TypeOK /\ [Next]_vars => TypeOK'
    <2> SUFFICES ASSUME TypeOK,
                        [Next]_vars
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. CASE L1
      <3> SUFFICES ASSUME 0 < Len(l1)
                   PROVE /\ v_eps' \in Int
                         /\ v_eps' >= 0
                         /\ v_delta' \in Int
                         /\ v_delta' >= 0
        BY <2>1 DEF L1, TypeOK, AbsLapSpec
      <3>1. CASE Len(l1) % Q = 0
        <4>1. v_eps' = v_eps + EpsDef * AbsVal((c1 + Head(l1)) - (c2 + Head(l2)))
          BY <2>1, <3>1 DEF L1, AbsLapSpec
        <4>2. v_delta' = v_delta
          BY <2>1, <3>1 DEF L1, AbsLapSpec
        <4> SUFFICES /\ AbsVal((c1 + Head(l1)) - (c2 + Head(l2))) \in Int
                     /\ AbsVal((c1 + Head(l1)) - (c2 + Head(l2))) >= 0
          BY <4>1, <4>2 DEF TypeOK, EpsDef
        <4>3. Head(l1) \in Int /\ Head(l2) \in Int
          BY <2>1, <3>1 DEF L1, TypeOK
        <4>4. /\ AbsVal((c1 + Head(l1)) - (c2 + Head(l2))) \in Int
              /\ AbsVal((c1 + Head(l1)) - (c2 + Head(l2))) >= 0
          BY <4>3 DEF AbsVal, TypeOK
        <4> QED
          BY <4>4
      <3>2. CASE Len(l1) % Q # 0
        <4>1. v_eps' = v_eps + EpsDef * AbsVal(Head(l1) - Head(l2))
          BY <2>1, <3>2 DEF L1, AbsLapSpec
        <4>2. v_delta' = v_delta
          BY <2>1, <3>2 DEF L1, AbsLapSpec
        <4> SUFFICES /\ AbsVal(Head(l1) - Head(l2)) \in Int
                     /\ AbsVal(Head(l1) - Head(l2)) >= 0
          BY <4>1, <4>2 DEF TypeOK, EpsDef
        <4>3. Head(l1) \in Int /\ Head(l2) \in Int
          BY <2>1, <3>2 DEF L1, TypeOK
        <4>4. /\ AbsVal(Head(l1) - Head(l2)) \in Int
              /\ AbsVal(Head(l1) - Head(l2)) >= 0
          BY <4>3 DEF AbsVal, TypeOK
        <4> QED
          BY <4>4
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

------------------------------------------------------------------------------
(* Initial relation between memories *)

Phi(lv1, lv2) == 
  /\ Len(lv1) = Len(lv2)
  /\ Len(lv1) # 0 => \E i \in 1..Len(lv1) : 
                        /\ AbsVal(lv1[i] - lv2[i]) <= 1
                        /\ \A j \in 1..Len(lv1) : j # i => lv1[j] = lv2[j]

THEOREM PhiInv == Phi(l1, l2) /\ Spec => []Phi(l1, l2)
  <1> SUFFICES ASSUME []TypeOK 
               PROVE  Phi(l1, l2) /\ Spec => []Phi(l1, l2)  
    BY PTL, TypeOKInv
  <1> SUFFICES ASSUME Phi(l1, l2), [Next]_vars 
               PROVE Phi(l1, l2)'
    BY PTL DEF Spec
  <1>1. Phi(l1, l2) /\ L1 => Phi(l1, l2)'
    <2> SUFFICES ASSUME Phi(l1, l2), L1, 0 < Len(l1)
                 PROVE Phi(l1, l2)'
      BY DEF L1
    <2>1. TypeOK
      BY PTL
    <2>2. /\ Len(l1) = Len(l2)
          /\ l1 \in Seq(Int)
          /\ 0 < Len(l1)
          /\ l2 \in Seq(Int)
          /\ 0 < Len(l2)
      BY <2>1 DEF TypeOK, L1, Phi
    <2> SUFFICES ASSUME Len(Tail(l1)) # 0
                 PROVE  \E i \in 1..Len(Tail(l1)) :
                           /\ AbsVal(Tail(l1)[i] - Tail(l2)[i]) <= 1
                           /\ \A j \in 1..Len(Tail(l1)) : j # i => Tail(l1)[j] = Tail(l2)[j]
      BY <2>2 DEF Phi, L1
    <2>3. PICK i_prev \in 1..Len(l1) :
          /\ AbsVal(l1[i_prev] - l2[i_prev]) <= 1
          /\ \A j \in 1..Len(l1) : j # i_prev => l1[j] = l2[j]
      BY DEF Phi
    <2>4. CASE i_prev = 1
      <3>1. \A j \in 1..Len(l1) : j # 1 => l1[j] = l2[j]
        BY <2>3, <2>4
      <3>2. Tail(l1) = Tail(l2)
        BY <2>2, <3>1
      <3>3. 1 \in 1..Len(Tail(l1)) (* Any index works *)
        BY <2>2, <2>3
      <3>4. AbsVal(Tail(l1)[1] - Tail(l2)[1]) <= 1
        BY <2>2, <3>2 DEF AbsVal
      <3>5. \A j \in 1..Len(Tail(l1)) : j # 1 => Tail(l1)[j] = Tail(l2)[j]
        BY <2>2, <3>2 
      <3> QED
        BY <3>3, <3>4, <3>5
    <2>5. CASE i_prev \in 2..Len(l1)
      <3> DEFINE i == i_prev - 1
      <3>1. i \in 1..Len(Tail(l1)) /\ i + 1 = i_prev
        BY <2>2, <2>5
      <3>2. AbsVal(Tail(l1)[i] - Tail(l2)[i]) <= 1
        BY <2>2, <2>3, <3>1 DEF AbsVal
      <3>3. \A j \in 1..Len(Tail(l1)) : j # i => Tail(l1)[j] = Tail(l2)[j]
        BY <2>2, <2>3, <3>1 
      <3> QED
        BY <3>1, <3>2, <3>3
    <2> QED
      BY <2>4, <2>5 
  <1>2. Phi(l1, l2) /\ L2 => Phi(l1, l2)'
    BY DEF L2, Phi
  <1>3. Phi(l1, l2) /\ Terminating => Phi(l1, l2)'
    BY DEF Terminating, vars, Phi
  <1>4. Phi(l1, l2) /\ UNCHANGED vars => Phi(l1, l2)'
    BY DEF vars, Phi
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4 DEF Next

------------------------------------------------------------------------------
(* Inductive invariant *)

IInv == /\ r1 = r2
        /\ next1 = next2
        /\ n1 = n2
        /\ v_delta = 0
        /\ AbsVal(c1 - c2) <= 1
        /\ l1 # l2 => v_eps = 0
        /\ c1 # c2 => (l1 = l2 /\ v_eps <= EpsDef)
        /\ l1 = l2 => v_eps <= 2 * EpsDef

THEOREM IndInv == Phi(l1, l2) /\ Spec => []IInv
  <1> SUFFICES ASSUME []TypeOK, []Phi(l1, l2) 
               PROVE  Spec => []IInv
    BY TypeOKInv, PhiInv
  <1>1. Init => IInv
    BY DEF Init, IInv, AbsVal, EpsDef
  <1>2. IInv /\ [Next]_vars => IInv'
    <2> SUFFICES ASSUME IInv,
                        [Next]_vars
                 PROVE  IInv'
      OBVIOUS
    <2>1. CASE L1
      <3>1. TypeOK /\ Phi(l1, l2) 
        BY PTL
      <3>2. /\ r1' = r2'
            /\ next1' = next2'
            /\ n1' = n2'
            /\ v_delta' = 0
        BY <3>1, <2>1 DEF L1, IInv, TypeOK, Phi, AbsVal, EpsDef, AbsLapSpec
      <3>3. (AbsVal(c1 - c2) <= 1)'
        BY <3>1, <2>1, SMTT(30) DEF L1, IInv, TypeOK, Phi, AbsVal, EpsDef, AbsLapSpec
      <3> SUFFICES /\ (l1' # l2' => v_eps' = 0)
                   /\ (c1' # c2' => (l1' = l2' /\ v_eps' <= EpsDef))
                   /\ (l1' = l2' => v_eps' <= 2 * EpsDef)
        BY <3>2, <3>3 DEF IInv
      <3> SUFFICES ASSUME /\ 0 < Len(l1)
                          /\ Len(l1) = Len(l2)
                   PROVE  /\ (l1' # l2' => v_eps' = 0)
                          /\ (c1' # c2' => (l1' = l2' /\ v_eps' <= EpsDef))
                          /\ (l1' = l2' => v_eps' <= 2 * EpsDef)
        BY <3>1, <2>1 DEF L1, IInv, Phi
      <3>4. CASE Len(l1) % Q = 0
        <4>1. c1' = c2'
          BY <2>1, <3>4 DEF L1
        <4>2. CASE c1 # c2
          <5>1. l1 = l2
            BY <4>2 DEF IInv
          <5>2. l1' = l2'
            BY <2>1, <5>1 DEF L1
          <5> SUFFICES v_eps' <= 2 * EpsDef
            BY <4>1, <5>2
          <5>3. v_eps <= EpsDef
            BY <4>2 DEF IInv
          <5>4. v_eps' = v_eps + EpsDef * AbsVal((c1 + Head(l1)) - (c2 + Head(l2)))
            BY <2>1, <3>4 DEF L1, AbsLapSpec
          <5>5. v_eps' = v_eps + EpsDef * AbsVal(c1 - c2)
            BY <3>1, <5>1, <5>4 DEF TypeOK
          <5> SUFFICES AbsVal(c1 - c2) <= 1
            BY <3>1, <5>3, <5>5 DEF EpsDef, AbsVal, TypeOK
          <5> QED
            BY DEF IInv
        <4>3. CASE c1 = c2
          <5>1. CASE l1 = l2
            <6>1. l1' = l2'
              BY <2>1, <5>1 DEF L1
            <6> SUFFICES v_eps' <= 2 * EpsDef
              BY <4>1, <6>1
            <6>2. v_eps' = v_eps + EpsDef * AbsVal((c1 + Head(l1)) - (c2 + Head(l2)))
              BY <2>1, <3>4 DEF L1, AbsLapSpec
            <6>3. v_eps' = v_eps
              BY <3>1, <4>3, <5>1, <6>2 DEF TypeOK, AbsVal, EpsDef
            <6> SUFFICES v_eps <= 2 * EpsDef
              BY <6>3
            <6> QED
              BY <5>1 DEF IInv
          <5>2. CASE l1 # l2
            <6>1. PICK i \in 1..Len(l1) : 
                     /\ AbsVal(l1[i] - l2[i]) <= 1
                     /\ \A j \in 1..Len(l1) : j # i => l1[j] = l2[j]
              BY <3>1 DEF Phi
            <6>2. CASE i = 1
              <7>1. \A j \in 1..Len(l1) : j # 1 => l1[j] = l2[j]
                BY <6>1, <6>2
              <7>2. Tail(l1) = Tail(l2)
                BY <3>1, <7>1 DEF TypeOK
              <7>3. l1' = l2'
                BY <2>1, <7>2 DEF L1
              <7> SUFFICES v_eps' <= 2 * EpsDef
                BY <4>1, <7>3
              <7>4. v_eps = 0
                BY <5>2 DEF IInv
              <7>5. v_eps' = v_eps + EpsDef * AbsVal((c1 + Head(l1)) - (c2 + Head(l2)))
                BY <2>1, <3>4 DEF L1, AbsLapSpec
              <7> SUFFICES AbsVal((c1 + Head(l1)) - (c2 + Head(l2))) <= 2
                BY <3>1, <7>4, <7>5 DEF EpsDef, AbsVal, TypeOK
              <7> SUFFICES AbsVal(Head(l1) - Head(l2)) <= 2
                BY <3>1, <4>3 DEF TypeOK, AbsVal
              <7> SUFFICES AbsVal(l1[1] - l2[1]) <= 1
                BY <3>1 DEF TypeOK, AbsVal
              <7> QED
                BY <6>1, <6>2
            <6>3. CASE i \in 2..Len(l1)
              <7>1. Head(l1) = Head(l2)
                BY <3>1, <6>1, <6>3 DEF TypeOK
              <7> SUFFICES v_eps' = 0
                BY <4>1 DEF EpsDef
              <7>2. AbsVal((c1 + Head(l1)) - (c2 + Head(l2))) = 0 
                BY <3>1, <4>3, <7>1 DEF TypeOK, AbsVal
              <7>3. v_eps' = v_eps + EpsDef * AbsVal((c1 + Head(l1)) - (c2 + Head(l2)))
                BY <2>1, <3>4 DEF L1, AbsLapSpec
              <7>4. v_eps' = v_eps
                BY <3>1, <7>2, <7>3 DEF EpsDef, TypeOK
              <7>5. v_eps = 0
                BY <5>2 DEF IInv
              <7> QED
                BY <7>4, <7>5
            <6> QED
              BY <6>1, <6>2, <6>3
          <5> QED
            BY <5>1, <5>2
        <4> QED 
          BY <4>2, <4>3
      <3>5. CASE Len(l1) % Q # 0
        <4>1. v_eps' = v_eps + EpsDef * AbsVal(Head(l1) - Head(l2))
          BY <2>1, <3>5 DEF L1, AbsLapSpec
        <4>2. CASE c1 # c2
          <5>1. l1 = l2 /\ v_eps <= EpsDef
            BY <4>2 DEF IInv
          <5>2. l1' = l2'
            BY <2>1, <5>1 DEF L1
          <5>3. TypeOK'
            BY PTL
          <5> SUFFICES v_eps' <= EpsDef 
            BY <3>1, <5>2, <5>3 DEF EpsDef, TypeOK
          <5>4. v_eps' = v_eps
            BY <3>1, <4>1, <5>1 DEF TypeOK, AbsVal, EpsDef
          <5> QED
            BY <5>1, <5>4
        <4>3. CASE c1 = c2
          <5>1. CASE l1 = l2
            <6>1. v_eps' = v_eps
              BY <3>1, <4>1, <5>1 DEF AbsVal, TypeOK, EpsDef
            <6> QED
              BY <2>1, <5>1, <6>1 DEF IInv, L1
          <5>2. CASE l1 # l2
            <6>1. v_eps = 0
              BY <5>2 DEF IInv
            <6>2. PICK i \in 1..Len(l1) : 
                     /\ AbsVal(l1[i] - l2[i]) <= 1
                     /\ \A j \in 1..Len(l1) : j # i => l1[j] = l2[j]
              BY <3>1 DEF Phi
            <6>3. CASE i = 1
              <7>1. \A j \in 1..Len(l1) : j # 1 => l1[j] = l2[j]
                BY <6>2, <6>3
              <7>2. Tail(l1) = Tail(l2)
                BY <3>1, <7>1 DEF TypeOK
              <7>3. l1' = l2'
                BY <2>1, <7>2 DEF L1
              <7>4. TypeOK'
                BY PTL
              <7> SUFFICES v_eps' <= EpsDef 
                BY <3>1, <7>3, <7>4 DEF TypeOK, EpsDef
              <7>5. AbsVal(Head(l1) - Head(l2)) <= 1
                BY <3>1, <6>2 DEF TypeOK, AbsVal
              <7> QED
                BY <3>1, <4>1, <6>1, <7>5 DEF TypeOK, AbsVal, EpsDef
            <6>4. CASE i \in 2..Len(l1)
              <7>1. Head(l1) = Head(l2)
                BY <3>1, <6>2, <6>4 DEF TypeOK
              <7>2. TypeOK'
                BY PTL
              <7>3. v_eps' = 0
                BY <3>1, <4>1, <6>1, <7>1 DEF AbsVal, TypeOK, EpsDef
              <7> SUFFICES c1' # c2' => l1' = l2'
                BY <3>1, <7>2, <7>3 DEF EpsDef, AbsVal, TypeOK
              <7> SUFFICES ASSUME c1' # c2'
                           PROVE  FALSE
                OBVIOUS
              <7>4. c1 # c2
                BY <2>1, <3>1, <3>5, <7>1 DEF L1, TypeOK
              <7> QED
                BY <4>3, <7>4
            <6> QED
              BY <6>2, <6>3, <6>4
          <5> QED
            BY <5>1, <5>2
        <4> QED
          BY <4>2, <4>3
      <3> QED
        BY <3>4, <3>5
    <2>2. CASE L2
      BY <2>2 DEF L2, IInv
    <2>3. CASE Terminating
      BY <2>3 DEF Terminating, vars, IInv
    <2>4. CASE UNCHANGED vars
      BY <2>4 DEF vars, IInv
    <2>5. QED
      BY <2>1, <2>2, <2>3, <2>4 DEF Next
  <1> QED
    BY <1>1, <1>2, PTL DEF Spec
               
------------------------------------------------------------------------------
(* Proof of (2 * EpsDef, 0)-DP w.r.t Phi *)

2EpsDef_0_DP == v_eps <= 2 * EpsDef /\ v_delta = 0 /\ out1 = out2

THEOREM DP == Phi(l1, l2) /\ Spec => [](pc = "Done" => 2EpsDef_0_DP)
  <1> SUFFICES ASSUME []TypeOK,
                      []Phi(l1, l2),
                      []IInv
               PROVE  Spec => [](pc = "Done" => 2EpsDef_0_DP)
    BY TypeOKInv, PhiInv, IndInv, PTL
  <1>1. Init => (pc = "Done" => 2EpsDef_0_DP)
    BY DEF Init
  <1>2. (pc = "Done" => 2EpsDef_0_DP) /\ [Next]_vars => (pc = "Done" => 2EpsDef_0_DP)'
    <2>1. CASE L1
      BY <2>1 DEF L1, 2EpsDef_0_DP
    <2>2. CASE L2
      <3>1. TypeOK /\ IInv
        BY PTL
      <3> QED
        BY <2>2, <3>1 DEF L2, 2EpsDef_0_DP, TypeOK, IInv, EpsDef
    <2>3. CASE Terminating
      BY <2>3 DEF Terminating, vars, 2EpsDef_0_DP
    <2>4. CASE UNCHANGED vars
      BY <2>4 DEF vars, 2EpsDef_0_DP
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4 DEF Next
  <1> QED
    BY <1>1, <1>2, PTL DEF Spec

=============================================================================