----------------------------- MODULE PTR_proof -------------------------------
EXTENDS PTR_transf, TLAPS

------------------------------------------------------------------------------
(***************************************************************************)
(* Defining notion of adjacency between initial memories, and proving that *)
(* this relation is conserved by the program.                              *)
(***************************************************************************)

Phi(db1, db2) == Dist[db1, db2] <= 1

PhiSpec ==
  /\ Spec
  /\ Phi(d1, d2)

THEOREM PhiInv == PhiSpec => []Phi(d1, d2)
  <1> SUFFICES ASSUME Phi(d1, d2), [Next]_vars
               PROVE  Phi(d1, d2)'
    BY PTL DEF PhiSpec, Spec
  <1>1. Phi(d1, d2) /\ L1 => Phi(d1, d2)'
    BY DEF L1, Phi
  <1>2. Phi(d1, d2) /\ L2 => Phi(d1, d2)'
    BY DEF L2, Phi
  <1>3. Phi(d1, d2) /\ L3 => Phi(d1, d2)'
    BY DEF L3, Phi
  <1>4. Phi(d1, d2) /\ L4 => Phi(d1, d2)'
    BY DEF L4, Phi
  <1>5. Phi(d1, d2) /\ L5 => Phi(d1, d2)'
    BY DEF L5, Phi
  <1>6. Phi(d1, d2) /\ Terminating => Phi(d1, d2)'
    BY DEF Terminating, vars, Phi
  <1>7. Phi(d1, d2) /\ UNCHANGED vars => Phi(d1, d2)'
    BY DEF vars, Phi
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 DEF Next

------------------------------------------------------------------------------
(***************)
(* Assumptions *)
(***************)

(* Assume domain of values is integers *)
ASSUMPTION ValDef ==
  Value = Int

ASSUMPTION QueryType == 
  Query \in [DBDomain -> QOutDomain]
    
ASSUMPTION DummyQOutType == 
  DummyQOut \in QOutDomain

ASSUMPTION DTIType ==
  DTI \in [QueryDomain \X DBDomain -> Nat]

ASSUMPTION DTISpec ==
  \A db1, db2 \in DBDomain :
    Dist[db1, db2] <= 1 => (
      \/ Query[db1] = Query[db2]
      \/ /\ DTI[Query, db1] = DTI[Query, db2]
         /\ DTI[Query, db1] = 0
    )

(* Arbitrary epsilon (positive real) *)
ASSUMPTION EpsDef == 
  /\ Epsilon \in Real
  /\ Epsilon > 0

ASSUMPTION TDef ==
  T \in Nat

ASSUMPTION DTIisOneSensitiveForQuery ==
  \A db1, db2 \in DBDomain :
    Dist[db1, db2] <= 1 => AbsVal(DTI[Query, db1] - DTI[Query, db2]) <= 1

------------------------------------------------------------------------------
(******************************)
(* Type correctness invariant *)
(******************************)

TypeOK == 
  /\ pc \in {"L1", "L2", "L3", "L4", "L5", "Done"}
  /\ d1 \in DBDomain
  /\ d2 \in DBDomain
  /\ x1 \in Nat
  /\ x2 \in Nat
  /\ y1 \in Value
  /\ y2 \in Value
  /\ out1 \in QOutDomain
  /\ out2 \in QOutDomain
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
      BY <2>1, QueryType, DTIType DEF L1, TypeOK, QueryDomain
    <2>2. CASE L2
      <3>1. PICK res \in AbsLap(Epsilon, x1, x2, v_eps, v_delta) :
              /\ v_delta' = res[4]
              /\ v_eps' = res[3]
              /\ y1' = res[1]
              /\ y2' = res[2]
        BY <2>2 DEF L2, TypeOK
      <3>2. /\ Epsilon \in Real
            /\ x1 \in Value
            /\ x2 \in Value
            /\ v_eps \in Real
            /\ v_delta \in Real
        BY ValDef, EpsDef DEF TypeOK
      <3>3. PICK n \in Value : 
              /\ res[1] = n
              /\ res[2] = n
              /\ res[3] = v_eps + Epsilon * AbsVal(x1 - x2)
              /\ res[4] = v_delta
        BY <3>1, <3>2, AbsLapHoareSpecDef DEF AbsLapHoareSpec
      <3> SUFFICES /\ v_eps + Epsilon * AbsVal(x1 - x2) \in Real
                   /\ v_eps + Epsilon * AbsVal(x1 - x2) >= 0
        BY <2>2, <3>1, <3>3 DEF TypeOK, L2
      <3>4. /\ v_eps \in Real
            /\ v_eps >= 0
            /\ Epsilon \in Real
            /\ AbsVal(x1 - x2) \in Nat
        BY ValDef, EpsDef DEF TypeOK, AbsVal
      <3> QED
        \* BY <3>4
        \* omitted due to lack of real arithmetic support
        OMITTED
    <2>3. CASE L3
      BY <2>3 DEF L3, TypeOK
    <2>4. CASE L4
      BY <2>4, QueryType DEF L4, TypeOK
    <2>5. CASE L5
      BY <2>5, DummyQOutType DEF L5, TypeOK
    <2>6. CASE Terminating
      BY <2>6 DEF Terminating, vars, TypeOK
    <2>7. CASE UNCHANGED vars
      BY <2>7 DEF vars, TypeOK
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
  <1> QED
    BY <1>1, <1>2, PTL DEF Spec

------------------------------------------------------------------------------
(***********************)
(* Inductive invariant *)
(***********************)

IInv == 
  /\ pc = "L1" => /\ v_eps = 0 
                  /\ v_delta = 0
  /\ pc = "L2" => /\ v_eps = 0 
                  /\ v_delta = 0 
                  /\ AbsVal(x1 - x2) <= 1 (* !!! *)
                  /\ \/ Query[d1] = Query[d2]
                     \/ (x1 = x2 /\ x1 = 0)
  /\ pc = "L3" => /\ v_eps <= Epsilon
                  /\ v_delta <= LapTail[Epsilon, T]
                  /\ y1 = y2
                  /\ \/ Query[d1] = Query[d2]
                     \/ /\ x1 = x2 
                        /\ x1 = 0
                        /\ AbsVal(y1 - x1) <= T
  /\ pc = "L4" => /\ Query[d1] = Query[d2]
                  /\ v_eps <= Epsilon
                  /\ v_delta <= LapTail[Epsilon, T]
  /\ pc = "L5" => /\ v_eps <= Epsilon
                  /\ v_delta <= LapTail[Epsilon, T]
  /\ pc = "Done" => /\ out1 = out2
                    /\ v_eps <= Epsilon
                    /\ v_delta <= LapTail[Epsilon, T] 

THEOREM IndInv == PhiSpec => []IInv
  <1> SUFFICES ASSUME []TypeOK,
                      []Phi(d1, d2)
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
      <3> SUFFICES /\ AbsVal(x1' - x2') <= 1
                   /\ \/ Query[d1] = Query[d2]
                      \/ (x1' = x2' /\ x1' = 0)
        BY <2>1 DEF L1, IInv
      <3>1. TypeOK /\ Phi(d1, d2)
        BY PTL
      <3>2. AbsVal(x1' - x2') <= 1
        <4>1. /\ x1' = DTI[Query, d1]
              /\ x2' = DTI[Query, d2]
          BY <2>1 DEF L1, IInv
        <4>2. AbsVal(DTI[Query, d1] - DTI[Query, d2]) <= 1
          BY <3>1, DTIisOneSensitiveForQuery DEF L1, IInv, TypeOK, Phi
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY <2>1, <3>1, <3>2, DTISpec DEF L1, IInv, TypeOK, Phi
    <2>2. CASE L2
      <3> SUFFICES /\ v_eps' <= Epsilon
                   /\ v_delta' <= LapTail[Epsilon, T]
                   /\ y1' = y2'
                   /\ \/ Query[d1] = Query[d2]
                      \/ /\ x1 = x2
                         /\ x1 = 0
                         /\ AbsVal(y1' - x1) <= T
        BY <2>2 DEF L2, IInv
      <3>1. TypeOK /\ Phi(d1, d2)
        BY PTL 
      <3>2. /\ v_eps = 0 
            /\ v_delta = 0
            /\ AbsVal(x1 - x2) <= 1
            /\ \/ Query[d1] = Query[d2]
               \/ (x1 = x2 /\ x1 = 0)
        BY <2>2 DEF L2, IInv
      <3>3. CASE Query[d1] = Query[d2]
        <4> SUFFICES /\ v_eps' <= Epsilon
                     /\ v_delta' <= LapTail[Epsilon, T]
                     /\ y1' = y2'
          BY <3>3
        <4>1. PICK res \in AbsLap(Epsilon, x1, x2, v_eps, v_delta) :
                /\ v_delta' = res[4]
                /\ v_eps' = res[3]
                /\ y1' = res[1]
                /\ y2' = res[2]
          BY <2>2 DEF L2
        <4>2. /\ Epsilon \in Real
              /\ x1 \in Value
              /\ x2 \in Value
              /\ v_eps \in Real
              /\ v_delta \in Real
          BY EpsDef, ValDef, <3>1 DEF TypeOK
        <4>3. PICK n \in Value :
              /\ res[1] = n
              /\ res[2] = n
              /\ res[3] = v_eps + Epsilon * AbsVal(x1 - x2)
              /\ res[4] = v_delta
          BY <4>1, <4>2, AbsLapHoareSpecDef DEF AbsLapHoareSpec
        <4>4. /\ n \in Value
              /\ y1' = n
              /\ y2' = n
              /\ v_eps' = v_eps + Epsilon * AbsVal(x1 - x2)
              /\ v_delta' = v_delta
          BY <4>1, <4>3
        <4> SUFFICES 0 + Epsilon * AbsVal(x1 - x2) <= Epsilon
          BY <3>2, <4>4, LapTailType, EpsDef, TDef
        <4>5. AbsVal(x1 - x2) <= 1
          BY <3>2
        <4> QED
          \* BY <4>5
          \* omitted due to lack of real arithmetic support
          OMITTED
      <3>4. CASE (x1 = x2 /\ x1 = 0)
        <4> SUFFICES /\ v_eps' <= Epsilon
                     /\ v_delta' <= LapTail[Epsilon, T]
                     /\ y1' = y2'
                     /\ AbsVal(y1' - x1) <= T
          BY <3>4
        <4>1. PICK res \in AbsLap(Epsilon, x1, x2, v_eps, v_delta) :
                /\ v_delta' = res[4]
                /\ v_eps' = res[3]
                /\ y1' = res[1]
                /\ y2' = res[2]
          BY <2>2 DEF L2
        <4>2. /\ Epsilon \in Real
              /\ T \in Nat
              /\ x1 \in Value
              /\ x2 \in Value
              /\ v_eps \in Real
              /\ v_delta \in Real
              /\ x1 = x2
          BY EpsDef, ValDef, TDef, <3>1, <3>4 DEF TypeOK
        <4>3. PICK n \in Value :
                /\ AbsVal(n - x1) <= T
                /\ res[1] = n
                /\ res[2] = n
                /\ res[3] = v_eps
                /\ res[4] = v_delta + LapTail[Epsilon, T]
          BY <4>1, <4>2, AbsLapAccSpecDef DEF AbsLapAccSpec
        <4>4. /\ n \in Value
              /\ AbsVal(n - x1) <= T
              /\ y1' = n
              /\ y2' = n
              /\ v_eps' = v_eps
              /\ v_delta' = v_delta + LapTail[Epsilon, T]
          BY <4>1, <4>3
        <4> SUFFICES /\ 0 <= Epsilon
                     /\ 0 + LapTail[Epsilon, T] <= LapTail[Epsilon, T]
          BY <3>2, <4>4
        <4> QED
          \* BY EpsDef, LapTailType
          \* Omitted due to lack of real arithmetic support
          OMITTED
      <3> QED
        BY <3>2, <3>3, <3>4
    <2>3. CASE L3
      <3> SUFFICES /\ pc' = "L4" => Query[d1] = Query[d2]
                   /\ v_eps <= Epsilon
                   /\ v_delta <= LapTail[Epsilon, T]
        BY <2>3 DEF L3, IInv
      <3>1. TypeOK /\ Phi(d1, d2)
        BY PTL
      <3>2. /\ v_eps <= Epsilon
            /\ v_delta <= LapTail[Epsilon, T]
            /\ y1 = y2
            /\ \/ Query[d1] = Query[d2]
               \/ /\ x1 = x2 
                  /\ x1 = 0
                  /\ AbsVal(y1 - x1) <= T
        BY <2>3 DEF L3, IInv
      <3>3. CASE AbsVal(y1) > T
        <4> SUFFICES Query[d1] = Query[d2]
          BY <3>2
        <4> SUFFICES ASSUME Query[d1] # Query[d2]
                     PROVE  FALSE
          OBVIOUS
        <4>1. /\ x1 = x2 
              /\ x1 = 0
              /\ AbsVal(y1 - x1) <= T
          BY <3>2
        <4>2. AbsVal(y1) <= T
          BY <3>1, <4>1, ValDef DEF TypeOK, AbsVal
        <4>3. AbsVal(y1) > T
          BY <3>3
        <4> QED
          BY <3>1, <4>2, <4>3, ValDef, TDef DEF TypeOK, AbsVal
      <3>4. CASE ~(AbsVal(y1) > T)
        BY <2>3, <3>4 DEF L3, IInv
      <3> QED
        BY <3>3, <3>4
    <2>4. CASE L4
      BY <2>4 DEF L4, IInv
    <2>5. CASE L5
      BY <2>5 DEF L5, IInv
    <2>6. CASE Terminating
      BY <2>6 DEF Terminating, vars, IInv
    <2>7. CASE UNCHANGED vars
      BY <2>7 DEF vars, IInv
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
  <1> QED
    BY <1>1, <1>2, PTL DEF Spec

------------------------------------------------------------------------------
(********************************************************)
(* Proof of (Epsilon, LapTail[Epsilon, T])-DP w.r.t Phi *)
(********************************************************)

(*************************************)
(* (Epsilon, LapTail[Epsilon, T])-DP *)
(*************************************)
DP ==
  pc = "Done" =>
    /\ out1 = out2
    /\ v_delta <= LapTail[Epsilon, T]
    /\ v_eps <= Epsilon

THEOREM DPThm == PhiSpec => []DP
  <1>1. IInv => DP
    BY DEF IInv, DP
  <1> SUFFICES PhiSpec => []IInv
    BY <1>1, PTL
  <1> QED
    BY IndInv
    
==============================================================================