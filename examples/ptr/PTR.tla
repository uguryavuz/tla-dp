--------------------------------- MODULE PTR ---------------------------------
EXTENDS Integers, DP

CONSTANTS DBDomain, QOutDomain, Epsilon, T

(* Distance function *)
DistDomain == [DBDomain \X DBDomain -> Nat]
Dist == CHOOSE f \in DistDomain : TRUE

(* Query function *)
QueryDomain == [DBDomain -> QOutDomain]
Query == CHOOSE q \in QueryDomain : TRUE

(* Distance to instability *)
DTI == CHOOSE dti \in [QueryDomain \X DBDomain -> Nat] : TRUE

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
    L2: y := Lap(Epsilon, x);
    L3: if (AbsVal(y) > T) {
    L4:   out := Query[d];
        } else {
    L5:   out := DummyQOut;
        };
  }
} *)

==============================================================================