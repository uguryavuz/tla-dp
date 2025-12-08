--------------------------------- MODULE PTR ---------------------------------
EXTENDS Integers, DP
CONSTANT DBDomain, QOutDomain

Dist == CHOOSE f \in [DBDomain \X DBDomain -> Nat] : TRUE
Query == CHOOSE q \in [DBDomain -> QOutDomain] : TRUE
DTI(q, d) == Max({x \in Nat : \A d_pr \in DBDomain : Dist[d, d_pr] <= x => q[d_pr] = q[d]})
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
    L1: x := DTI(Query, d);
    L2: y := Lap(x);
    L3: if (Epsilon * AbsVal(y) > InvLog(Delta)) {
          out := Query[d];
        } else {
          out := DummyQOut;
        };
  }
} *)

==============================================================================