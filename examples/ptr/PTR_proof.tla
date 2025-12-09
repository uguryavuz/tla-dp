----------------------------- MODULE PTR_proof -------------------------------
EXTENDS PTR_transf, TLAPS

------------------------------------------------------------------------------
(* Initial relation between memories *)
Phi(db1, db2) == Dist[db1, db2] <= 1

THEOREM PhiInv == Phi(d1, d2) /\ Spec => []Phi(d1, d2)
  <1> SUFFICES ASSUME Phi(d1, d2), [Next]_vars
               PROVE  Phi(d1, d2)'
    BY PTL DEF Spec
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
(* DTI related assumptions *)
LEMMA DTIWellDefined == 
    /\ DTI[Query, d1] \in Real
    /\ DTI[Query, d2] \in Real
  OMITTED

ASSUMPTION DTISpec ==
  \A d1, d2 \in DBDomain :
    Dist[d1, d2] <= 1 => (
      \/ Query[d1] = Query[d2]
      \/ /\ DTI[Query, d1] = DTI[Query, d2]
         /\ DTI[Query, d1] = 0
    )

(* DP parameter assumptions *)
ASSUMPTION ParamAsspts ==
  /\ Epsilon \in Real
  /\ Delta \in Real
  /\ Epsilon >= 0
  /\ Delta > 0

(* Query related assumptions *)
ASSUMPTION QueryType == Query \in [DBDomain -> QOutDomain]
ASSUMPTION DummyQOutType == DummyQOut \in QOutDomain

(* Type correctness invariant *)
TypeOK == /\ pc \in {"L1", "L2", "L3", "L4", "L5", "Done"}
          /\ d1 \in DBDomain
          /\ d2 \in DBDomain
          /\ x1 \in Real
          /\ x2 \in Real
          /\ y1 \in Real
          /\ y2 \in Real
          /\ out1 \in QOutDomain
          /\ out2 \in QOutDomain
          /\ v_eps \in Real
          /\ v_delta \in Real

THEOREM TypeOKInv == Spec => []TypeOK
  <1>1. Init => TypeOK
    <2> SUFFICES 0 \in Real
      BY DEF Init, TypeOK
    <2> QED
      BY ZeroIsReal
  <1>2. TypeOK /\ [Next]_vars => TypeOK'
    <2> SUFFICES ASSUME TypeOK,
                        [Next]_vars
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. CASE L1
      <3> SUFFICES /\ DTI[Query, d1] \in Real
                   /\ DTI[Query, d2] \in Real
        BY <2>1 DEF L1, TypeOK
      <3> QED
        BY DTIWellDefined
    <2>2. CASE L2
      <3>1. PICK res \in AbsLap(x1, x2, v_eps, v_delta) :
            /\ v_delta' = res[4]
            /\ v_eps' = res[3]
            /\ y1' = res[1]
            /\ y2' = res[2]
        BY <2>2 DEF L2, TypeOK
      <3> SUFFICES res \in Real \X Real \X Real \X Real
        BY <2>2, <3>1 DEF L2, TypeOK
      <3> QED
        BY <3>1, AbsLapHoareSpecForReals DEF TypeOK
    <2>3. CASE L3
      BY <2>3 DEF L3, TypeOK
    <2>4. CASE L4
      <3> SUFFICES /\ Query[d1] \in QOutDomain
                   /\ Query[d2] \in QOutDomain
        BY <2>4 DEF L4, TypeOK
      <3> QED
        BY QueryType DEF TypeOK
    <2>5. CASE L5
      <3> SUFFICES DummyQOut \in QOutDomain
        BY <2>5 DEF L5, TypeOK
      <3> QED
        BY DummyQOutType DEF TypeOK
    <2>6. CASE Terminating
      BY <2>6 DEF Terminating, vars, TypeOK
    <2>7. CASE UNCHANGED vars
      BY <2>7 DEF vars, TypeOK
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
  <1> QED
    BY <1>1, <1>2, PTL DEF Spec

------------------------------------------------------------------------------
(* Inductive invariant *)
IInv == 
  /\ pc = "L1" => /\ v_eps = 0 
                  /\ v_delta = 0
  /\ pc = "L2" => /\ v_eps = 0 
                  /\ v_delta = 0 
                  /\ AbsVal(x1 - x2) <= 1 (* !!! *)
                  /\ \/ Query[d1] = Query[d2]
                     \/ (x1 = x2 /\ x1 = 0)
  /\ pc = "L3" => /\ v_eps <= Epsilon
                  /\ v_delta <= Delta
                  /\ y1 = y2
                  /\ \/ Query[d1] = Query[d2]
                     \/ /\ x1 = x2 
                        /\ x1 = 0
                        /\ Epsilon * AbsVal(y1 - x1) <= NegLog[Delta]
  /\ pc = "L4" => /\ Query[d1] = Query[d2]
                  /\ v_eps <= Epsilon
                  /\ v_delta <= Delta
  /\ pc = "L5" => /\ v_eps <= Epsilon
                  /\ v_delta <= Delta
  /\ pc = "Done" => /\ out1 = out2
                    /\ v_eps <= Epsilon
                    /\ v_delta <= Delta 

ASSUMPTION DTIisOneSensitiveForQuery ==
  \A d1, d2 \in DBDomain :
    Dist[d1, d2] <= 1 =>
      AbsVal(DTI[Query, d1] - DTI[Query, d2]) <= 1

THEOREM IndInv == Phi(d1, d2) /\ Spec => []IInv
  <1> SUFFICES ASSUME []TypeOK,
                      []Phi(d1, d2)
               PROVE  Spec => []IInv
    BY TypeOKInv, PhiInv, PTL
  <1>0. TypeOK /\ Phi(d1, d2)
    BY PTL
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
      <3>1. AbsVal(x1' - x2') <= 1
        <4>1. /\ x1' = DTI[Query, d1]
              /\ x2' = DTI[Query, d2]
          BY <2>1 DEF L1, IInv
        <4>2. AbsVal(DTI[Query, d1] - DTI[Query, d2]) <= 1
          BY DTIisOneSensitiveForQuery, <1>0 DEF L1, IInv, TypeOK, Phi
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY <1>0, <2>1, <3>1, DTISpec DEF L1, IInv, Phi, TypeOK
    <2>2. CASE L2
      <3> SUFFICES /\ v_eps' <= Epsilon
                   /\ v_delta' <= Delta
                   /\ y1' = y2'
                   /\ \/ Query[d1] = Query[d2]
                      \/ /\ x1 = x2 
                         /\ x1 = 0
                         /\ Epsilon * AbsVal(y1' - x1) <= NegLog[Delta]
        BY <2>2 DEF L2, IInv
      <3>1. /\ v_eps = 0
            /\ v_delta = 0
            /\ AbsVal(x1 - x2) <= 1
            /\ \/ Query[d1] = Query[d2]
               \/ (x1 = x2 /\ x1 = 0)
        BY <2>2 DEF L2, IInv
      <3>2. CASE Query[d1] = Query[d2]
        <4> SUFFICES /\ v_eps' <= Epsilon
                     /\ v_delta' <= Delta
                     /\ y1' = y2'
          BY <3>2 DEF L2, IInv
        <4>1. PICK res \in AbsLap(x1, x2, v_eps, v_delta) :
              /\ v_delta' = res[4]
              /\ v_eps' = res[3]
              /\ y1' = res[1]
              /\ y2' = res[2]
          BY <2>2, <3>1 DEF L2, IInv
        <4>2. /\ res \in Real \X Real \X Real \X Real
              /\ res[1] = res[2]
              /\ res[3] = v_eps + Epsilon * AbsVal(x1 - x2)
              /\ res[4] = v_delta
          BY <1>0, <4>1, AbsLapHoareSpecForReals DEF TypeOK
        <4> SUFFICES /\ v_eps' <= Epsilon
                     /\ v_delta' <= Delta
          BY <4>1, <4>2
        <4>3. v_delta' <= Delta
          <5>1. v_delta' = v_delta
            BY <4>1, <4>2
          <5>2. v_delta = 0
            BY <2>2 DEF L2, IInv
          <5> SUFFICES 0 <= Delta
            BY <5>1, <5>2
          <5> SUFFICES 0 < Delta
            OBVIOUS
          <5> QED
            BY ParamAsspts
        <4>4. v_eps' <= Epsilon
          <5>1. v_eps' = v_eps + Epsilon * AbsVal(x1 - x2)
            BY <4>1, <4>2
          <5>2. v_eps = 0
            BY <2>2 DEF L2, IInv
          <5>3. v_eps' = 0 + Epsilon * AbsVal(x1 - x2)
            BY <5>1, <5>2
          <5> SUFFICES 0 + Epsilon * AbsVal(x1 - x2) <= Epsilon
            BY <5>1, <5>2, <5>3
          <5> SUFFICES AbsVal(x1 - x2) <= 1 => 0 + Epsilon * AbsVal(x1 - x2) <= Epsilon
            BY <3>1
          <5> QED
            OMITTED
        <4> QED
          BY <4>3, <4>4
      <3>3. CASE (x1 = x2 /\ x1 = 0)
        <4> SUFFICES /\ v_eps' <= Epsilon
                     /\ v_delta' <= Delta
                     /\ y1' = y2'
                     /\ Epsilon * AbsVal(y1' - x1) <= NegLog[Delta]
          BY <3>3 DEF L2, IInv
        <4>1. PICK res \in AbsLap(x1, x2, v_eps, v_delta) :
              /\ v_delta' = res[4]
              /\ v_eps' = res[3]
              /\ y1' = res[1]
              /\ y2' = res[2]
          BY <2>2, <3>1 DEF L2, IInv
        <4>2. /\ res \in Real \X Real \X Real \X Real
              /\ res[1] = res[2]
              /\ Epsilon * AbsVal(res[1] - x1) <= NegLog[Delta]
              /\ res[3] = v_eps
              /\ res[4] = v_delta + Delta
          BY <1>0, <3>3, <4>1, AbsLapAccSpecForReals DEF TypeOK
        <4> SUFFICES /\ v_eps' <= Epsilon
                     /\ v_delta' <= Delta
          BY <4>1, <4>2
        <4>3. v_eps' = 0 /\ v_delta' = 0 + Delta
          BY <2>2, <4>1, <4>2 DEF IInv, L2
        <4>4. 0 <= Epsilon
          BY ParamAsspts
        <4> SUFFICES 0 + Delta <= Delta
          BY <4>3, <4>4
        <4> QED
          OMITTED
      <3> QED
        BY <3>1, <3>2, <3>3  
    <2>3. CASE L3
      <3>1. /\ v_eps <= Epsilon
            /\ v_delta <= Delta
            /\ y1 = y2
            /\ \/ Query[d1] = Query[d2]
               \/ /\ x1 = x2 
                  /\ x1 = 0
                  /\ Epsilon * AbsVal(y1 - x1) <= NegLog[Delta]
        BY <2>3 DEF L3, IInv
      <3>2. CASE Epsilon * AbsVal(y1) > NegLog[Delta]
        <4> SUFFICES Query[d1] = Query[d2]
          BY <2>3, <3>1, <3>2 DEF L3, IInv
        <4> SUFFICES ASSUME Query[d1] # Query[d2]
                     PROVE  FALSE
          OBVIOUS
        <4>1. /\ x1 = x2 
              /\ x1 = 0
              /\ Epsilon * AbsVal(y1 - x1) <= NegLog[Delta]
          BY <3>1
        <4>2. Epsilon * AbsVal(y1 - 0) <= NegLog[Delta]
          BY <4>1
        <4>3. Epsilon * AbsVal(y1) > NegLog[Delta]
          BY <3>2
        <4> SUFFICES (/\ Epsilon * AbsVal(y1 - 0) <= NegLog[Delta] 
                      /\ Epsilon * AbsVal(y1) > NegLog[Delta]) => FALSE
          BY <4>2, <4>3
        <4> QED
          OMITTED
      <3>3. CASE ~(Epsilon * AbsVal(y1) > NegLog[Delta])
        BY <2>3, <3>3 DEF L3, IInv
      <3> QED
        BY <3>2, <3>3
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

==============================================================================