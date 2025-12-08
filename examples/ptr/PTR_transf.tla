--------------------------------- MODULE PTR_transf ---------------------------------
EXTENDS Integers, DP
CONSTANT DBDomain, QOutDomain

Dist == CHOOSE f \in [DBDomain \X DBDomain -> Nat] : TRUE
Query == CHOOSE q \in [DBDomain -> QOutDomain] : TRUE
DTI(q, d) == Max({x \in Nat : \A d_pr \in DBDomain : Dist[d, d_pr] <= x => q[d_pr] = q[d]})
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
    L1: x1 := DTI(Query, d1) || x2 := DTI(Query, d2);
    L2: with (res \in AbsLap(x1, x2, v_eps, v_delta)) {
          y1 := res[1] || y2 := res[2] || v_eps := res[3] || v_delta := res[4]
        };
    L3: await ((Epsilon * AbsVal(y1) > InvLog(Delta)) = (Epsilon * AbsVal(y2) > InvLog(Delta))); if (Epsilon * AbsVal(y1) > InvLog(Delta)) {
          out1 := Query[d1] || out2 := Query[d2];
        } else {
          out1 := DummyQOut || out2 := DummyQOut;
        };
  }
} *)
\* BEGIN TRANSLATION (chksum(pcal) = "480fb9db" /\ chksum(tla) = "cb88c5a8")
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
      /\ /\ x1' = DTI(Query, d1)
         /\ x2' = DTI(Query, d2)
      /\ pc' = "L2"
      /\ UNCHANGED << d1, d2, y1, y2, out1, out2, v_eps, v_delta >>

L2 == /\ pc = "L2"
      /\ \E res \in AbsLap(x1, x2, v_eps, v_delta):
           /\ v_delta' = res[4]
           /\ v_eps' = res[3]
           /\ y1' = res[1]
           /\ y2' = res[2]
      /\ pc' = "L3"
      /\ UNCHANGED << d1, d2, x1, x2, out1, out2 >>

L3 == /\ pc = "L3"
      /\ ((Epsilon * AbsVal(y1) > InvLog(Delta)) = (Epsilon * AbsVal(y2) > InvLog(Delta)))
      /\ IF Epsilon * AbsVal(y1) > InvLog(Delta)
            THEN /\ /\ out1' = Query[d1]
                    /\ out2' = Query[d2]
            ELSE /\ /\ out1' = DummyQOut
                    /\ out2' = DummyQOut
      /\ pc' = "Done"
      /\ UNCHANGED << d1, d2, x1, x2, y1, y2, v_eps, v_delta >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == L1 \/ L2 \/ L3
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

==============================================================================
