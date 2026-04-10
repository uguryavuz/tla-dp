--------------------------------- MODULE DTI ---------------------------------
EXTENDS Integers, DP, TLAPS, NaturalsInduction
CONSTANT DBDomain, QOutDomain

(* Query domain *)
QueryDomain == [DBDomain -> QOutDomain]

(* Distance function: arbitrary function satisfying metric axioms *)
Dist == 
  CHOOSE f \in [DBDomain \X DBDomain -> Nat] : 
    /\ \A d1, d2 \in DBDomain : f[d1, d2] = 0 => d1 = d2
    /\ \A d1, d2 \in DBDomain : f[d1, d2] = f[d2, d1]
    /\ \A d1, d2, d3 \in DBDomain : f[d1, d3] <= f[d1, d2] + f[d2, d3]

THEOREM DistExists ==
    \E f \in [DBDomain \X DBDomain -> Nat] : 
      /\ \A d1, d2 \in DBDomain : f[d1, d2] = 0 => d1 = d2
      /\ \A d1, d2 \in DBDomain : f[d1, d2] = f[d2, d1]
      /\ \A d1, d2, d3 \in DBDomain : f[d1, d3] <= f[d1, d2] + f[d2, d3]
  <1> DEFINE f == [d1d2 \in DBDomain \X DBDomain |-> 
                     IF d1d2[1] = d1d2[2] THEN 0 ELSE 1]
  <1>1. f \in [DBDomain \X DBDomain -> Nat]
    OBVIOUS
  <1>2. \A d1, d2 \in DBDomain : f[d1, d2] = 0 => d1 = d2
    OBVIOUS
  <1>3. \A d1, d2 \in DBDomain : f[d1, d2] = f[d2, d1]
    OBVIOUS
  <1>4. \A d1, d2, d3 \in DBDomain : f[d1, d3] <= f[d1, d2] + f[d2, d3]
    OBVIOUS
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4

THEOREM DistType ==
    Dist \in [DBDomain \X DBDomain -> Nat]
  BY DistExists DEF Dist

THEOREM DistIdentityOfIndiscernibles ==
    \A d1, d2 \in DBDomain : Dist[d1, d2] = 0 => d1 = d2
  BY DistExists DEF Dist

THEOREM DistSymmetry ==
    \A d1, d2 \in DBDomain : Dist[d1, d2] = Dist[d2, d1]
  BY Zenon, DistExists DEF Dist

THEOREM DistTriangleInequality ==
    \A d1, d2, d3 \in DBDomain : Dist[d1, d3] <= Dist[d1, d2] + Dist[d2, d3]
  BY Zenon, DistExists DEF Dist

(* Distance to instability *)
StableRadii(q, d) == 
  {x \in Nat : \A d_pr \in DBDomain : Dist[d, d_pr] <= x => q[d_pr] = q[d]}
    
UnstableRadii(q, d) == 
  {x \in Nat : \E d_pr \in DBDomain : Dist[d, d_pr] <= x /\ q[d_pr] # q[d]}
    
DTI == [qd \in QueryDomain \X DBDomain |->
  CHOOSE x \in StableRadii(qd[1], qd[2]) : 
    \A y \in StableRadii(qd[1], qd[2]) : y <= x]

NonConstantQuery(q) ==
  \E d1, d2 \in DBDomain : q[d1] # q[d2]

THEOREM DTIDefinition ==
    \A q \in QueryDomain, d \in DBDomain :
      NonConstantQuery(q) =>
        /\ DTI[q, d] \in Nat
        /\ DTI[q, d] \in StableRadii(q, d)
        /\ \A y \in StableRadii(q, d) : y <= DTI[q, d] 
  <1> SUFFICES ASSUME NEW q \in QueryDomain,
                      NEW d \in DBDomain,
                      NonConstantQuery(q)
               PROVE  /\ DTI[q, d] \in Nat
                      /\ DTI[q, d] \in StableRadii(q, d)
                      /\ \A y \in StableRadii(q, d) : y <= DTI[q, d]
    OBVIOUS
  <1>1. DTI[q, d] = CHOOSE x \in StableRadii(q, d) : \A y \in StableRadii(q, d) : y <= x
    BY Zenon DEF DTI
  <1> SUFFICES \E x \in StableRadii(q, d) : \A y \in StableRadii(q, d) : y <= x
    BY <1>1 DEF StableRadii
  <1>2. UnstableRadii(q, d) # {}
    <2> SUFFICES \E x \in Nat : \E d_pr \in DBDomain : Dist[d, d_pr] <= x /\ q[d_pr] # q[d]
      BY DEF UnstableRadii
    <2> SUFFICES \E d_pr \in DBDomain : q[d_pr] # q[d]
      BY DistType
    <2>1. PICK d1, d2 \in DBDomain : q[d1] # q[d2]
      BY DEF NonConstantQuery
    <2>2. CASE q[d] = q[d1]
      BY <2>1, <2>2
    <2>3. CASE q[d] = q[d2]
      BY <2>1, <2>3
    <2>4. CASE q[d] # q[d1] /\ q[d] # q[d2]
      BY <2>4
    <2> QED
      BY <2>2, <2>3, <2>4
  <1>3. \E m \in UnstableRadii(q, d) : \A n \in UnstableRadii(q, d) : m <= n
    <2> DEFINE P(k) == k \in UnstableRadii(q, d)
    <2>1. \E m \in Nat : P(m) /\ \A k \in 0 .. m-1 : ~ P(k)
      <3>1. PICK n0 \in Nat : P(n0)
        BY <1>2 DEF UnstableRadii
      <3> HIDE DEF P
      <3> QED
        BY <3>1, SmallestNatural, Isa
    <2>2. PICK m \in UnstableRadii(q, d) : \A k \in 0 .. m-1 : k \notin UnstableRadii(q, d)
      BY <2>1
    <2> SUFFICES ASSUME NEW n \in UnstableRadii(q, d) 
                 PROVE  m <= n
      BY <2>2
    <2>3. UnstableRadii(q, d) \in SUBSET Nat /\ UnstableRadii(q, d) # {}
      BY <1>2 DEF UnstableRadii
    <2> QED
      BY <2>2, <2>3
  <1>4. PICK min_unst \in UnstableRadii(q, d) : \A n \in UnstableRadii(q, d) : min_unst <= n
    BY <1>3 DEF UnstableRadii
  <1>5. min_unst > 0
    BY DistIdentityOfIndiscernibles, DistType DEF UnstableRadii
  <1> DEFINE max_st == min_unst - 1
  <1>6. max_st \in Nat
    BY <1>5 DEF UnstableRadii
  <1> SUFFICES max_st \in StableRadii(q, d) /\ \A y \in StableRadii(q, d) : y <= max_st
    BY <1>6, Zenon DEF UnstableRadii, StableRadii
  <1>7. max_st \in StableRadii(q, d)
    BY <1>4, <1>6 DEF UnstableRadii, StableRadii
  <1> SUFFICES ASSUME NEW y \in StableRadii(q, d)
               PROVE  y <= max_st
    BY <1>7
  <1> SUFFICES ASSUME y >= min_unst
               PROVE  y \in UnstableRadii(q, d)
    BY DEF UnstableRadii, StableRadii
  <1> QED
    BY DistType DEF UnstableRadii, StableRadii

LEMMA SuccessorOfDTIisLeastUnstableRadius ==
    \A q \in QueryDomain, d \in DBDomain :
      NonConstantQuery(q) =>
        /\ DTI[q, d] + 1 \in UnstableRadii(q, d)
        /\ \A x \in UnstableRadii(q, d) : DTI[q, d] + 1 <= x 
  <1> SUFFICES ASSUME NEW q \in QueryDomain,
                      NEW d \in DBDomain,
                      NonConstantQuery(q)
               PROVE  /\ DTI[q, d] + 1 \in UnstableRadii(q, d)
                      /\ \A x \in UnstableRadii(q, d) : DTI[q, d] + 1 <= x
    OBVIOUS
  <1>1. /\ DTI[q, d] \in StableRadii(q, d)
        /\ \A y \in StableRadii(q, d) : y <= DTI[q, d]
    BY DTIDefinition
  <1>2. DTI[q, d] + 1 \in UnstableRadii(q, d)
    BY <1>1 DEF UnstableRadii, StableRadii
  <1> SUFFICES ASSUME NEW x \in UnstableRadii(q, d)
               PROVE  DTI[q, d] + 1 <= x
    BY <1>2
  <1> SUFFICES ASSUME x <= DTI[q, d]
               PROVE  x \in StableRadii(q, d)
    BY <1>1 DEF UnstableRadii, StableRadii
  <1> QED
    BY <1>1, DistType DEF UnstableRadii, StableRadii

LEMMA ShiftStableRadius ==
    ASSUME NEW q \in QueryDomain,
           NonConstantQuery(q),
           NEW d1 \in DBDomain, 
           NEW d2 \in DBDomain,
           Dist[d1, d2] <= 1,
           NEW r \in StableRadii(q, d1) \ {0}
    PROVE  r - 1 \in StableRadii(q, d2)
  <1> SUFFICES ASSUME NEW d \in DBDomain,
                      Dist[d, d2] <= r - 1
               PROVE  q[d] = q[d2]
    BY DistSymmetry DEF StableRadii
  <1>1. Dist[d, d1] <= Dist[d, d2] + 1
    <2>1. Dist[d, d1] <= Dist[d, d2] + Dist[d1, d2]
      BY DistTriangleInequality, DistSymmetry
    <2> QED
      BY <2>1, DistType
  <1>2. Dist[d, d1] <= r
    BY <1>1, DistType DEF StableRadii
  <1>3. q[d] = q[d1]
    BY <1>2, DistSymmetry DEF StableRadii
  <1>4. q[d1] = q[d2]
    BY DistType DEF StableRadii
  <1> QED
    BY <1>3, <1>4

THEOREM DTIHasSensitivityOne ==
    \A q \in QueryDomain : NonConstantQuery(q) =>
      \A d1, d2 \in DBDomain : Dist[d1, d2] <= 1 =>
        AbsVal(DTI[q, d1] - DTI[q, d2]) <= 1
  <1> SUFFICES ASSUME NEW q \in QueryDomain,
                      NonConstantQuery(q),
                      NEW d1 \in DBDomain, 
                      NEW d2 \in DBDomain,
                      Dist[d1, d2] <= 1
               PROVE  AbsVal(DTI[q, d1] - DTI[q, d2]) <= 1
    OBVIOUS
  <1> DEFINE k1 == DTI[q, d1]
  <1> DEFINE k2 == DTI[q, d2]
  <1>1. k1 \in StableRadii(q, d1) /\ \A x \in StableRadii(q, d1) : x <= k1
    BY DTIDefinition
  <1>2. k2 \in StableRadii(q, d2) /\ \A x \in StableRadii(q, d2) : x <= k2
    BY DTIDefinition
  <1>3. k1 <= k2 + 1
    <2> SUFFICES ASSUME k1 > 0
                 PROVE  k1 <= k2 + 1
      BY <1>1, <1>2 DEF StableRadii
    <2>1. \A r \in 1..k1 : r \in StableRadii(q, d1)
      BY <1>1, DistType DEF StableRadii
    <2>2. \A r \in 1..k1 : r-1 \in StableRadii(q, d2)
      BY <1>1, <2>1, ShiftStableRadius DEF StableRadii
    <2>3. 0 \in StableRadii(q, d2)
      BY DistIdentityOfIndiscernibles, DistType DEF StableRadii
    <2>4. k1 - 1 \in StableRadii(q, d2)
      BY <1>1, <2>2, <2>3 DEF StableRadii
    <2>5. k1 - 1 <= k2
      BY <1>2, <2>4
    <2> QED
      BY <1>1, <1>2, <2>5 DEF StableRadii
  <1>4. k2 <= k1 + 1
    <2> SUFFICES ASSUME k2 > 0
                 PROVE  k2 <= k1 + 1
      BY <1>2, <1>1 DEF StableRadii
    <2>1. \A r \in 1..k2 : r \in StableRadii(q, d2)
      BY <1>2, DistType DEF StableRadii
    <2>2. \A r \in 1..k2 : r-1 \in StableRadii(q, d1)
      <3> SUFFICES ASSUME NEW r \in 1..k2
                   PROVE  r-1 \in StableRadii(q, d1)
        OBVIOUS
      <3>1. r \in StableRadii(q, d2) \ {0}
        BY <2>1 DEF StableRadii
      <3>2. Dist[d2, d1] <= 1
        BY DistSymmetry
      <3>3. r-1 \in StableRadii(q, d1)
        BY <3>1, <3>2, ShiftStableRadius DEF StableRadii
      <3> QED
        BY <3>3
    <2>3. 0 \in StableRadii(q, d1)
      BY DistIdentityOfIndiscernibles, DistType DEF StableRadii
    <2>4. k2 - 1 \in StableRadii(q, d1)
      BY <1>2, <2>2, <2>3 DEF StableRadii
    <2>5. k2 - 1 <= k1
      BY <1>1, <2>4
    <2> QED
      BY <1>2, <1>1, <2>5 DEF StableRadii
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4 DEF AbsVal, StableRadii

THEOREM DTISpec ==
    \A q \in QueryDomain : NonConstantQuery(q) =>
      \A d1, d2 \in DBDomain : Dist[d1, d2] <= 1 =>
        \/ q[d1] = q[d2]
        \/ /\ DTI[q, d1] = 0
           /\ DTI[q, d2] = 0
  <1> SUFFICES ASSUME NEW q \in QueryDomain,
                      NonConstantQuery(q),
                      NEW d1 \in DBDomain, 
                      NEW d2 \in DBDomain,
                      Dist[d1, d2] <= 1
               PROVE  \/ q[d1] = q[d2]
                      \/ /\ DTI[q, d1] = 0
                         /\ DTI[q, d2] = 0
    OBVIOUS
  <1> SUFFICES ASSUME q[d1] # q[d2]
               PROVE  /\ DTI[q, d1] = 0
                      /\ DTI[q, d2] = 0
    OBVIOUS
  <1>1. DTI[q, d1] = 0
    <2>1. /\ DTI[q, d1] \in StableRadii(q, d1)
          /\ \A y \in StableRadii(q, d1) : y <= DTI[q, d1] 
      BY DTIDefinition
    <2>2. 1 \in UnstableRadii(q, d1)
      BY DistType DEF UnstableRadii
    <2>3. \A x \in Nat : x >= 1 => x \in UnstableRadii(q, d1)
      BY <2>2, DistType DEF UnstableRadii
    <2> QED
      BY <2>1, <2>3 DEF UnstableRadii, StableRadii
  <1>2. DTI[q, d2] = 0
    <2>1. /\ DTI[q, d2] \in StableRadii(q, d2)
          /\ \A y \in StableRadii(q, d2) : y <= DTI[q, d2] 
      BY DTIDefinition
    <2>2. 1 \in UnstableRadii(q, d2)
      BY DistType, DistSymmetry DEF UnstableRadii
    <2>3. \A x \in Nat : x >= 1 => x \in UnstableRadii(q, d2)
      BY <2>2, DistType DEF UnstableRadii
    <2> QED
      BY <2>1, <2>3 DEF UnstableRadii, StableRadii
  <1> QED
    BY <1>1, <1>2

==============================================================================
