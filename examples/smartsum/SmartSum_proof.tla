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
        BY SMTT(30), EpsDef, QDef, ValDef, AbsLapHoareSpecDef, <2>1 
          DEF L1, TypeOK, AbsLapHoareSpec
      <3>1. CASE Len(l1) % Q = 1
        <4>1. PICK res \in AbsLap(Epsilon, c1 + Head(l1), c2 + Head(l2), v_eps, v_delta):
              /\ v_delta' = res[4]
              /\ v_eps' = res[3]
              /\ x1' = res[1]
              /\ x2' = res[2]
          BY <2>1, <3>1 DEF TypeOK, L1
        <4>2. /\ Epsilon \in Real
              /\ c1 + Head(l1) \in Value
              /\ c2 + Head(l2) \in Value
              /\ v_eps \in Real
              /\ v_delta \in Real
          BY EpsDef, ValDef, <2>1 DEF TypeOK, L1
        <4>3. /\ v_eps' = v_eps + Epsilon * AbsVal((c1 + Head(l1)) - (c2 + Head(l2)))
              /\ v_delta' = v_delta
          BY <4>1, <4>2, AbsLapHoareSpecDef DEF AbsLapHoareSpec
        <4>4. /\ v_delta' \in Real
              /\ v_delta' >= 0
          BY <4>3 DEF TypeOK
        <4> SUFFICES v_eps' \in Real /\ v_eps' >= 0
          BY <4>4
        <4>5. v_eps \in Real /\ v_eps >= 0
          BY DEF TypeOK
        <4>6. AbsVal((c1 + Head(l1)) - (c2 + Head(l2))) \in Int /\ AbsVal((c1 + Head(l1)) - (c2 + Head(l2))) >= 0
          BY ValDef, <4>2 DEF AbsVal
        <4>7. Epsilon \in Real /\ Epsilon > 0
          BY EpsDef
        <4> QED
          \* BY <4>5, <4>6, <4>7
          \* omitted due to lack of real arithmetic support
          OMITTED
      <3>2. CASE Len(l1) % Q # 1
        <4>1. PICK res \in AbsLap(Epsilon, Head(l1), Head(l2), v_eps, v_delta):
              /\ v_delta' = res[4]
              /\ v_eps' = res[3]
              /\ x1' = res[1]
              /\ x2' = res[2]
          BY <2>1, <3>2 DEF TypeOK, L1
        <4>2. /\ Epsilon \in Real
              /\ Head(l1) \in Value
              /\ Head(l2) \in Value
              /\ v_eps \in Real
              /\ v_delta \in Real
          BY EpsDef, ValDef, <2>1 DEF TypeOK, L1
        <4>3. /\ v_eps' = v_eps + Epsilon * AbsVal(Head(l1) - Head(l2))
              /\ v_delta' = v_delta
          BY <4>1, <4>2, AbsLapHoareSpecDef DEF AbsLapHoareSpec
        <4>4. /\ v_delta' \in Real
              /\ v_delta' >= 0
          BY <4>3 DEF TypeOK
        <4> SUFFICES v_eps' \in Real /\ v_eps' >= 0
          BY <4>4
        <4>5. v_eps \in Real /\ v_eps >= 0
          BY DEF TypeOK
        <4>6. AbsVal(Head(l1) - Head(l2)) \in Int /\ AbsVal(Head(l1) - Head(l2)) >= 0
          BY ValDef, <4>2 DEF AbsVal
        <4>7. Epsilon \in Real /\ Epsilon > 0
          BY EpsDef
        <4> QED
          \* BY <4>5, <4>6, <4>7
          \* omitted due to lack of real arithmetic support
          OMITTED
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
(***************************************************************************)
(* Defining notion of adjacency between initial memories, and proving that *)
(* this relation is conserved by the program.                              *)
(***************************************************************************)

Phi(lv1, lv2) == 
  /\ Len(lv1) = Len(lv2)
  /\ Len(lv1) # 0 => \E i \in 1..Len(lv1) : 
                        /\ AbsVal(lv1[i] - lv2[i]) <= 1
                        /\ \A j \in 1..Len(lv1) : j # i => lv1[j] = lv2[j]

PhiSpec ==
  /\ Spec
  /\ Phi(l1, l2)

THEOREM PhiInv == PhiSpec => []Phi(l1, l2)
  <1> SUFFICES ASSUME []TypeOK
               PROVE  Phi(l1, l2) /\ Spec => []Phi(l1, l2)
    BY PTL, TypeOKInv DEF PhiSpec
  <1> SUFFICES ASSUME Phi(l1, l2), [Next]_vars
               PROVE  Phi(l1, l2)'
    BY PTL DEF Spec
  <1> SUFFICES [Next]_vars => Phi(l1', l2')
    BY DEF Phi
  <1>1. [Next]_vars => Phi(l1', l2')
    <2>0. TypeOK /\ TypeOK'
      BY PTL
    <2>1. CASE L1
      <3> SUFFICES ASSUME /\ Len(l1) = Len(l2)
                          /\ 0 < Len(l1)
                          /\ l1 \in Seq(Value)
                          /\ l2 \in Seq(Value)
                   PROVE  Phi(l1', l2')
        BY <2>0, <2>1 DEF TypeOK, L1, Phi
      <3>1. /\ l1' = Tail(l1)
            /\ l2' = Tail(l2)
        BY <2>1 DEF L1
      <3> SUFFICES ASSUME Len(l1') # 0
                   PROVE  \E i \in 1..Len(l1') : 
                            /\ AbsVal(l1'[i] - l2'[i]) <= 1
                            /\ \A j \in 1..Len(l1') : j # i => l1'[j] = l2'[j]
        BY <3>1 DEF Phi
      <3>2. PICK i_prev \in 1..Len(l1) : 
              /\ AbsVal(l1[i_prev] - l2[i_prev]) <= 1
              /\ \A j \in 1..Len(l1) : j # i_prev => l1[j] = l2[j]
        BY <2>1 DEF Phi
      <3>3. CASE i_prev = 1
        <4>1. \A j \in 1..Len(l1) : j # 1 => l1[j] = l2[j]
          BY <3>2, <3>3
        <4>2. l1' = l2'
          BY <3>1, <4>1
        <4>3. 1 \in 1..Len(l1') (* Any index works *)
          BY <3>1
        <4>4. AbsVal(l1'[1] - l2'[1]) <= 1
          BY <4>2, <4>3, <2>0, ValDef DEF AbsVal, TypeOK
        <4>5. \A j \in 1..Len(l1') : j # 1 => l1'[j] = l2'[j]
          BY <4>2, <4>3
        <4> QED
          BY <4>3, <4>4, <4>5
      <3>4. CASE i_prev \in 2..Len(l1)
        <4> DEFINE i == i_prev - 1
        <4>1. i \in 1..Len(l1') /\ i + 1 = i_prev
          BY <3>1, <3>4
        <4>2. AbsVal(l1'[i] - l2'[i]) <= 1
          BY <3>1, <3>2, <3>4
        <4>3. \A j \in 1..Len(l1') : j # i => l1'[j] = l2'[j]
          BY <3>1, <3>2, <3>4
        <4> QED
          BY <4>1, <4>2, <4>3
      <3> QED
        BY <3>2, <3>3, <3>4
    <2>2. CASE L2
      BY <2>2 DEF L2, Phi
    <2>3. CASE Terminating
      BY <2>3 DEF Terminating, Phi, vars
    <2>4. CASE UNCHANGED vars
      BY <2>4 DEF vars, Phi
    <2>5. QED
      BY <2>1, <2>2, <2>3, <2>4 DEF Next
  <1> QED
    BY <1>1

------------------------------------------------------------------------------
(***********************)
(* Inductive invariant *)
(***********************)

IInv == 
  /\ r1 = r2
  /\ next1 = next2
  /\ n1 = n2
  /\ v_delta = 0
  /\ AbsVal(c1 - c2) <= 1
  /\ l1 # l2 => v_eps = 0
  /\ c1 # c2 => (l1 = l2 /\ v_eps <= Epsilon)
  /\ l1 = l2 => v_eps <= 2 * Epsilon

THEOREM IndInv == PhiSpec => []IInv
  <1> SUFFICES ASSUME []TypeOK,
                      []Phi(l1, l2)
               PROVE  Spec => []IInv
    BY TypeOKInv, PhiInv DEF PhiSpec
  <1>1. Init => IInv
    <2> SUFFICES ASSUME Init
                 PROVE  v_eps <= 2 * Epsilon
      BY DEF Init, IInv, AbsVal
    <2>1. v_eps = 0
      BY DEF Init
    <2> SUFFICES 0 <= 2 * Epsilon
      BY <2>1
    <2> QED
      \* BY EpsDef
      \* omitted due to lack of real arithmetic support
      OMITTED
  <1>2. IInv /\ [Next]_vars => IInv'
    <2> SUFFICES ASSUME IInv,
                        [Next]_vars
                 PROVE  IInv'
      OBVIOUS
    <2>1. CASE L1
      <3>1. /\ TypeOK
            /\ TypeOK'
            /\ Phi(l1, l2)
        BY PTL
      <3>2. CASE 0 < Len(l1) /\ Len(l1) % Q = 1
        <4>1. PICK res \in AbsLap(Epsilon, c1 + Head(l1), c2 + Head(l2), v_eps, v_delta):
                /\ v_delta' = res[4]
                /\ v_eps' = res[3]
                /\ x1' = res[1]
                /\ x2' = res[2]
          BY <2>1, <3>2 DEF TypeOK, Phi, L1
        <4>2. /\ Epsilon \in Real
              /\ c1 + Head(l1) \in Value
              /\ c2 + Head(l2) \in Value
              /\ v_eps \in Real
              /\ v_delta \in Real
          BY EpsDef, ValDef, <2>1, <3>1, <3>2 DEF TypeOK, L1
        <4>3. PICK n \in Value : 
                /\ res[1] = n
                /\ res[2] = n
                /\ res[3] = v_eps + Epsilon * AbsVal((c1 + Head(l1)) - (c2 + Head(l2)))
                /\ res[4] = v_delta
          BY <4>1, <4>2, AbsLapHoareSpecDef DEF AbsLapHoareSpec
        <4>4. /\ n \in Value
              /\ x1' = n
              /\ x2' = n
              /\ v_eps' = v_eps + Epsilon * AbsVal((c1 + Head(l1)) - (c2 + Head(l2)))
              /\ v_delta' = v_delta
          BY <4>1, <4>3
        <4> SUFFICES 
              /\ l1' # l2' => v_eps' = 0
              /\ l1' = l2' => v_eps' <= 2 * Epsilon
          BY <2>1, <3>2, <4>4 DEF IInv, L1, AbsVal
        <4>5. CASE c1 # c2
          <5>1. l1 = l2 /\ v_eps <= Epsilon
            BY <4>5 DEF IInv
          <5>2. l1' = l2'
            BY <2>1, <5>1 DEF L1
          <5>3. v_eps' = v_eps + Epsilon * AbsVal((c1 + Head(l1)) - (c2 + Head(l2)))
            BY <4>4
          <5>4. AbsVal((c1 + Head(l1)) - (c2 + Head(l2))) = AbsVal(c1 - c2)
            BY <5>1, <3>1, <3>2, ValDef DEF TypeOK, AbsVal
          <5>5. v_eps' = v_eps + Epsilon * AbsVal(c1 - c2)
            BY <5>3, <5>4
          <5>6. /\ v_eps <= Epsilon
                /\ AbsVal(c1 - c2) <= 1
            BY <5>1 DEF IInv
          <5> QED
            \* BY <5>5, <5>6, EpsDef
            \* omitted due to lack of real arithmetic support
            OMITTED
        <4>6. CASE c1 = c2 /\ l1 = l2
          <5>1. l1' = l2'
            BY <2>1, <4>6 DEF L1
          <5> SUFFICES v_eps' <= 2 * Epsilon
            BY <5>1
          <5>2. AbsVal((c1 + Head(l1)) - (c2 + Head(l2))) = 0
            BY <3>1, <3>2, <4>6, ValDef DEF TypeOK, AbsVal
          <5>3. v_eps' = v_eps + Epsilon * 0
            BY <4>4, <5>2
          <5>4. v_eps <= 2 * Epsilon
            BY <4>6 DEF IInv
          <5> QED
            \* BY <5>3, <5>4, EpsDef
            \* omitted due to lack of real arithmetic support
            OMITTED
        <4>7. CASE c1 = c2 /\ l1 # l2
          <5>1. v_eps = 0
            BY <4>7 DEF IInv
          <5>2. PICK i \in 1..Len(l1) : 
                  /\ AbsVal(l1[i] - l2[i]) <= 1
                  /\ \A j \in 1..Len(l1) : j # i => l1[j] = l2[j]
            BY <3>1, <3>2 DEF Phi
          <5>3. CASE i = 1
            <6>1. l1' = l2'
              BY <2>1, <3>1, <3>2, <5>2, <5>3 DEF Phi, TypeOK, L1
            <6>2. AbsVal((c1 + Head(l1)) - (c2 + Head(l2))) = AbsVal(l1[1] - l2[1])
              BY <3>1, <4>7, <5>3, ValDef DEF TypeOK, AbsVal, Phi
            <6>3. v_eps = 0
              BY <4>7 DEF IInv
            <6>4. v_eps' = 0 + Epsilon * AbsVal(l1[1] - l2[1])
              BY <4>4, <6>2, <6>3
            <6> SUFFICES 0 + Epsilon * AbsVal(l1[1] - l2[1]) <= 2 * Epsilon
              BY <6>1, <6>4
            <6>5. AbsVal(l1[1] - l2[1]) <= 1
              BY <5>2, <5>3
            <6> QED
              \* BY <6>5, EpsDef
              \* omitted due to lack of real arithmetic support
              OMITTED
          <5>4. CASE i \in 2..Len(l1)
            <6>1. Head(l1) = Head(l2)
              BY <3>1, <5>2, <5>4 DEF TypeOK
            <6>2. AbsVal((c1 + Head(l1)) - (c2 + Head(l2))) = 0
              BY <6>1, <4>7, <3>1, ValDef DEF TypeOK, AbsVal
            <6>3. v_eps' = v_eps + Epsilon * 0
              BY <4>4, <6>2
            <6>4. v_eps = 0
              BY <4>7 DEF IInv
            <6> SUFFICES /\ 0 + Epsilon * 0 <= 2 * Epsilon
                         /\ 0 + Epsilon * 0 = 0
              BY <6>3, <6>4
            <6> QED
              \* BY EpsDef
              \* omitted due to lack of real arithmetic support
              OMITTED
          <5> QED
            BY <5>3, <5>4
        <4> QED
          BY <4>5, <4>6, <4>7
      <3>3. CASE 0 < Len(l1) /\ Len(l1) % Q # 1
        <4>1. PICK res \in AbsLap(Epsilon, Head(l1), Head(l2), v_eps, v_delta):
                /\ v_delta' = res[4]
                /\ v_eps' = res[3]
                /\ x1' = res[1]
                /\ x2' = res[2]
          BY <2>1, <3>3 DEF TypeOK, Phi, L1
        <4>2. /\ Epsilon \in Real
              /\ Head(l1) \in Value
              /\ Head(l2) \in Value
              /\ v_eps \in Real
              /\ v_delta \in Real
          BY EpsDef, ValDef, <2>1, <3>1, <3>3 DEF TypeOK, L1
        <4>3. PICK n \in Value : 
                /\ res[1] = n
                /\ res[2] = n
                /\ res[3] = v_eps + Epsilon * AbsVal(Head(l1) - Head(l2))
                /\ res[4] = v_delta
          BY <4>1, <4>2, AbsLapHoareSpecDef DEF AbsLapHoareSpec
        <4>4. /\ n \in Value
              /\ x1' = n
              /\ x2' = n
              /\ v_eps' = v_eps + Epsilon * AbsVal(Head(l1) - Head(l2))
              /\ v_delta' = v_delta
          BY <4>1, <4>3
        <4> SUFFICES 
              /\ AbsVal(c1' - c2') <= 1
              /\ l1' # l2' => v_eps' = 0
              /\ c1' # c2' => (l1' = l2' /\ v_eps' <= Epsilon)
              /\ l1' = l2' => v_eps' <= 2 * Epsilon
          BY <2>1, <3>3, <4>4 DEF IInv, L1, AbsVal
        <4>5. CASE c1 # c2
          <5>1. l1 = l2 /\ v_eps <= Epsilon
            BY <4>5 DEF IInv
          <5>2. l1' = l2'
            BY <2>1, <5>1 DEF L1
          <5>3. AbsVal(c1' - c2') = AbsVal(c1 - c2)
            BY <5>1, <3>1, <3>3, <2>1, ValDef DEF TypeOK, AbsVal, L1
          <5>4. AbsVal(c1 - c2) <= 1
            BY DEF IInv
          <5>5. v_eps' = v_eps + Epsilon * 0
            BY <5>1, <4>4, <3>1, <3>3, ValDef DEF TypeOK, AbsVal
          <5> SUFFICES /\ v_eps + Epsilon * 0 <= Epsilon
                       /\ v_eps + Epsilon * 0 <= 2 * Epsilon
            BY <5>2, <5>3, <5>4, <5>5
          <5>6. v_eps <= Epsilon
            BY <5>1
          <5> QED
            \* BY <5>6, EpsDef
            \* omitted due to lack of real arithmetic support
            OMITTED
        <4>6. CASE c1 = c2 /\ l1 = l2
          <5>1. v_eps' = v_eps + Epsilon * 0
            BY <4>4, <4>6, <3>1, <3>3, ValDef DEF TypeOK, AbsVal
          <5>2. l1' = l2'
            BY <2>1, <4>6 DEF L1
          <5>3. c1' = c2'
            BY <2>1, <4>6 DEF L1
          <5> SUFFICES v_eps + Epsilon * 0 <= 2 * Epsilon
            BY <5>1, <5>2, <5>3, <3>1, ValDef DEF AbsVal, TypeOK
          <5>4. v_eps <= 2 * Epsilon
            BY <4>6 DEF IInv
          <5> QED
            \* BY <5>4, EpsDef
            \* omitted due to lack of real arithmetic support
            OMITTED
        <4>7. CASE c1 = c2 /\ l1 # l2
          <5>1. v_eps = 0
            BY <4>7 DEF IInv
          <5>2. PICK i \in 1..Len(l1) : 
                  /\ AbsVal(l1[i] - l2[i]) <= 1
                  /\ \A j \in 1..Len(l1) : j # i => l1[j] = l2[j]
            BY <3>1, <3>3 DEF Phi
          <5>3. CASE i = 1
            <6>1. l1' = l2'
              BY <2>1, <3>1, <3>3, <5>2, <5>3 DEF Phi, TypeOK, L1
            <6>2. AbsVal(Head(l1) - Head(l2)) <= 1
              BY <5>2, <5>3, ValDef DEF TypeOK, AbsVal, Phi
            <6>3. AbsVal(c1' - c2') <= 1
              BY <4>7, <6>2, <3>1, <3>3, <2>1, ValDef DEF TypeOK, AbsVal, L1
            <6> SUFFICES /\ v_eps' <= Epsilon
                         /\ v_eps' <= 2 * Epsilon
              BY <6>1, <6>3
            <6>4. v_eps' = 0 + Epsilon * AbsVal(Head(l1) - Head(l2))
              BY <4>4, <5>1
            <6> SUFFICES /\ 0 + Epsilon * AbsVal(Head(l1) - Head(l2)) <= Epsilon
                         /\ 0 + Epsilon * AbsVal(Head(l1) - Head(l2)) <= 2 * Epsilon
              BY <6>4
            <6> QED
              \* BY <6>2, EpsDef
              \* omitted due to lack of real arithmetic support
              OMITTED
          <5>4. CASE i \in 2..Len(l1)
            <6>1. Head(l1) = Head(l2)
              BY <3>1, <5>2, <5>4 DEF TypeOK
            <6>2. c1' = c2'
              BY <2>1, <4>7, <6>1 DEF L1
            <6>3. AbsVal(c1' - c2') <= 1
              BY <3>1, <6>2, ValDef DEF TypeOK, AbsVal
            <6> SUFFICES /\ v_eps' = 0
                         /\ v_eps' <= Epsilon
                         /\ v_eps' <= 2 * Epsilon
              BY <6>2, <6>3
            <6>4. v_eps' = 0 + Epsilon * 0
              BY <4>4, <5>1, <3>1, <6>1, ValDef DEF TypeOK, AbsVal
            <6> SUFFICES /\ 0 + Epsilon * 0 = 0
                         /\ 0 + Epsilon * 0 <= Epsilon
                         /\ 0 + Epsilon * 0 <= 2 * Epsilon
              BY <6>4
            <6> QED
              \* BY EpsDef
              \* omitted due to lack of real arithmetic support
              OMITTED
          <5> QED
            BY <5>3, <5>4
        <4> QED
          BY <4>5, <4>6, <4>7
      <3>4. CASE ~(0 < Len(l1))
        BY <2>1, <3>4 DEF L1, IInv
      <3> QED
        BY <3>2, <3>3, <3>4
    <2>2. CASE L2
      BY <2>2 DEF L2, IInv
    <2>3. CASE Terminating
      BY <2>3 DEF Terminating, IInv, vars
    <2>4. CASE UNCHANGED vars
      BY <2>4 DEF vars, IInv
    <2>5. QED
      BY <2>1, <2>2, <2>3, <2>4 DEF Next
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

THEOREM DPThm == PhiSpec => []DP
  <1> SUFFICES ASSUME []TypeOK, []Phi(l1, l2), []IInv
               PROVE  Spec => []DP
    BY TypeOKInv, PhiInv, IndInv DEF PhiSpec
  <1>1. Init => DP
    BY DEF Init, DP
  <1>2. DP /\ [Next]_vars => DP'
    <2>1. CASE L1
      BY <2>1 DEF L1, DP
    <2>2. CASE L2
      <3>1. TypeOK /\ IInv /\ IInv'
        BY PTL
      <3> SUFFICES ASSUME DP /\ [Next]_vars,
                          (pc = "Done")'
                    PROVE  (/\ out1 = out2
                            /\ v_delta = 0
                            /\ v_eps <= 2 * Epsilon)'
        BY DEF DP
      <3>2. (out1 = out2)'
        BY <2>2, <3>1 DEF L2, DP, IInv
      <3>3. (v_delta = 0)'
        BY <2>2, <3>1 DEF L2, DP, IInv
      <3>4. v_eps' = 0 \/ v_eps' <= 2 * Epsilon
        BY <3>1 DEF IInv
      <3>5. (v_eps' <= 2 * Epsilon)
        \* BY <3>4
        \* Omitted due to lack of real arithmetic support
        OMITTED
      <3> QED
        BY <3>2, <3>3, <3>5
    <2>3. CASE Terminating
      BY <2>3 DEF Terminating, DP, vars
    <2>4. CASE UNCHANGED vars
      BY <2>4 DEF vars, DP
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4 DEF Next
  <1> QED
    BY <1>1, <1>2, PTL DEF Spec

==============================================================================
