--------------------------------- MODULE PTR ---------------------------------
EXTENDS Integers, DP
CONSTANT DBDomain, QOutDomain

(* Distance function *)
DistDomain == [DBDomain \X DBDomain -> Real]
Dist == CHOOSE f \in DistDomain : TRUE

(* Query function *)
QueryDomain == [DBDomain -> QOutDomain]
Query == CHOOSE q \in QueryDomain : TRUE

(* Distance to instability *)
\* DTI(q, d) == Max({x \in Nat : \A d_pr \in DBDomain : Dist[d, d_pr] <= x => q[d_pr] = q[d]})
DTI == CHOOSE dti \in [QueryDomain \X DistDomain -> Real] : TRUE

(* Dummy query output *)
DummyQOut == CHOOSE qo \in QOutDomain : TRUE

(*--algorithm PTR {
  variables
    (* inputs *)
    d \in DBDomain,
    (* registers *)
    x = 0,
    y = 0,
    (* return register *)
    out \in QOutDomain;
  {
    L1: x := DTI[Query, d];
    L2: y := Lap(x);
    L3: if (Epsilon * AbsVal(y) > NegLog[Delta]) {
    L4:   out := Query[d];
        } else {
    L5:   out := DummyQOut;
        };
  }
} *)

==============================================================================