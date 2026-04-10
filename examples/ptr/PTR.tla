--------------------------------- MODULE PTR ---------------------------------
EXTENDS DTI (* Extends Integers and DP *)
CONSTANTS Epsilon, T (* DBDomain and QOutDomain declared in DTI *)

(* Query function *)
Query == CHOOSE q \in QueryDomain : NonConstantQuery(q)

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
