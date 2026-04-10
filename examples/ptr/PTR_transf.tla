--------------------------------- MODULE PTR_transf ---------------------------------
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
    d1 \in DBDomain, d2 \in DBDomain,
    (* registers *)
    x1 = 0, x2 = 0,
    y1 = 0, y2 = 0,
    (* return register *)
    out1 \in QOutDomain, out2 \in QOutDomain,
    (* Privacy cost variables *)
    v_eps = 0,
    v_delta = 0;
  {
    L1: x1 := DTI[Query, d1] || x2 := DTI[Query, d2];
    L2: with (res \in AbsLap(Epsilon, x1, x2, v_eps, v_delta)) {
          y1 := res[1] || y2 := res[2] || v_eps := res[3] || v_delta := res[4]
        };
    L3: await ((AbsVal(y1) > T) = (AbsVal(y2) > T)); if (AbsVal(y1) > T) {
    L4:   out1 := Query[d1] || out2 := Query[d2];
        } else {
    L5:   out1 := DummyQOut || out2 := DummyQOut;
        };
  }
} *)
\* BEGIN TRANSLATION (chksum(pcal) = "99ac5003" /\ chksum(tla) = "4e7fd207")
VARIABLES pc, d1, d2, x1, x2, y1, y2, out1, out2, v_eps, v_delta

vars == << pc, d1, d2, x1, x2, y1, y2, out1, out2, v_eps, v_delta >>

Init == (* Global variables *)
        /\ d1 \in DBDomain
        /\ d2 \in DBDomain
        /\ x1 = 0
        /\ x2 = 0
        /\ y1 = 0
        /\ y2 = 0
        /\ out1 \in QOutDomain
        /\ out2 \in QOutDomain
        /\ v_eps = 0
        /\ v_delta = 0
        /\ pc = "L1"

L1 == /\ pc = "L1"
      /\ /\ x1' = DTI[Query, d1]
         /\ x2' = DTI[Query, d2]
      /\ pc' = "L2"
      /\ UNCHANGED << d1, d2, y1, y2, out1, out2, v_eps, v_delta >>

L2 == /\ pc = "L2"
      /\ \E res \in AbsLap(Epsilon, x1, x2, v_eps, v_delta):
           /\ v_delta' = res[4]
           /\ v_eps' = res[3]
           /\ y1' = res[1]
           /\ y2' = res[2]
      /\ pc' = "L3"
      /\ UNCHANGED << d1, d2, x1, x2, out1, out2 >>

L3 == /\ pc = "L3"
      /\ ((AbsVal(y1) > T) = (AbsVal(y2) > T))
      /\ IF AbsVal(y1) > T
            THEN /\ pc' = "L4"
            ELSE /\ pc' = "L5"
      /\ UNCHANGED << d1, d2, x1, x2, y1, y2, out1, out2, v_eps, v_delta >>

L4 == /\ pc = "L4"
      /\ /\ out1' = Query[d1]
         /\ out2' = Query[d2]
      /\ pc' = "Done"
      /\ UNCHANGED << d1, d2, x1, x2, y1, y2, v_eps, v_delta >>

L5 == /\ pc = "L5"
      /\ /\ out1' = DummyQOut
         /\ out2' = DummyQOut
      /\ pc' = "Done"
      /\ UNCHANGED << d1, d2, x1, x2, y1, y2, v_eps, v_delta >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == L1 \/ L2 \/ L3 \/ L4 \/ L5
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

==============================================================================
