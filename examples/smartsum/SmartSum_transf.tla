------------------------------ MODULE SmartSum_transf ------------------------------
EXTENDS Integers, Sequences, DP
CONSTANT Q

(*--algorithm SmartSum {
    variables
    (* inputs *)
    l1 \in Seq(Value), l2 \in Seq(Value),
    (* registers *)
    next1 = 0, next2 = 0,
    n1 = 0, n2 = 0,
    c1 = 0, c2 = 0,
    x1 = 0, x2 = 0,
    r1 = <<>>, r2 = <<>>,
    (* return register *)
    out1 = <<>>, out2 = <<>>,
    (* Privacy cost variables *)
    v_eps = 0,
    v_delta = 0;
  {
    L1: while (0 < Len(l1)) { await ((0 < Len(l1)) = (0 < Len(l2)));
          await ((Len(l1) % Q = 0) = (Len(l2) % Q = 0)); if (Len(l1) % Q = 0) {
            with (res \in AbsLap(c1 + Head(l1), c2 + Head(l2), v_eps, v_delta)) {
              x1 := res[1] || x2 := res[2] || v_eps := res[3] || v_delta := res[4]
            }; 
            n1 := x1 + n1 || n2 := x2 + n2;
            next1 := n1 || next2 := n2;
            c1 := 0 || c2 := 0;
            r1 := Append(r1, next1) || r2 := Append(r2, next2);
          } else {
            with (res \in AbsLap(Head(l1), Head(l2), v_eps, v_delta)) {
              x1 := res[1] || x2 := res[2] || v_eps := res[3] || v_delta := res[4]
            };
            next1 := next1 + x1 || next2 := next2 + x2;
            c1 := c1 + Head(l1) || c2 := c2 + Head(l2);
            r1 := Append(r1, next1) || r2 := Append(r2, next2);
          }; 
          l1 := Tail(l1) || l2 := Tail(l2);
        }; await ((0 < Len(l1)) = (0 < Len(l2)));
    L2: out1 := r1 || out2 := r2; 
  }
} *)
\* BEGIN TRANSLATION (chksum(pcal) = "5891aff7" /\ chksum(tla) = "37b4b9ad")
VARIABLES pc, l1, l2, next1, next2, n1, n2, c1, c2, x1, x2, r1, r2, out1, 
          out2, v_eps, v_delta

vars == << pc, l1, l2, next1, next2, n1, n2, c1, c2, x1, x2, r1, r2, out1, 
           out2, v_eps, v_delta >>

Init == (* Global variables *)
        /\ l1 \in Seq(Value)
        /\ l2 \in Seq(Value)
        /\ next1 = 0
        /\ next2 = 0
        /\ n1 = 0
        /\ n2 = 0
        /\ c1 = 0
        /\ c2 = 0
        /\ x1 = 0
        /\ x2 = 0
        /\ r1 = <<>>
        /\ r2 = <<>>
        /\ out1 = <<>>
        /\ out2 = <<>>
        /\ v_eps = 0
        /\ v_delta = 0
        /\ pc = "L1"

L1 == /\ pc = "L1"
      /\ IF 0 < Len(l1)
            THEN /\ ((0 < Len(l1)) = (0 < Len(l2)))
                 /\ ((Len(l1) % Q = 0) = (Len(l2) % Q = 0))
                 /\ IF Len(l1) % Q = 0
                       THEN /\ \E res \in AbsLap(c1 + Head(l1), c2 + Head(l2), v_eps, v_delta):
                                 /\ v_delta' = res[4]
                                 /\ v_eps' = res[3]
                                 /\ x1' = res[1]
                                 /\ x2' = res[2]
                            /\ /\ n1' = x1' + n1
                               /\ n2' = x2' + n2
                            /\ /\ next1' = n1'
                               /\ next2' = n2'
                            /\ /\ c1' = 0
                               /\ c2' = 0
                            /\ /\ r1' = Append(r1, next1')
                               /\ r2' = Append(r2, next2')
                       ELSE /\ \E res \in AbsLap(Head(l1), Head(l2), v_eps, v_delta):
                                 /\ v_delta' = res[4]
                                 /\ v_eps' = res[3]
                                 /\ x1' = res[1]
                                 /\ x2' = res[2]
                            /\ /\ next1' = next1 + x1'
                               /\ next2' = next2 + x2'
                            /\ /\ c1' = c1 + Head(l1)
                               /\ c2' = c2 + Head(l2)
                            /\ /\ r1' = Append(r1, next1')
                               /\ r2' = Append(r2, next2')
                            /\ UNCHANGED << n1, n2 >>
                 /\ /\ l1' = Tail(l1)
                    /\ l2' = Tail(l2)
                 /\ pc' = "L1"
            ELSE /\ ((0 < Len(l1)) = (0 < Len(l2)))
                 /\ pc' = "L2"
                 /\ UNCHANGED << l1, l2, next1, next2, n1, n2, c1, c2, x1, x2, 
                                 r1, r2, v_eps, v_delta >>
      /\ UNCHANGED << out1, out2 >>

L2 == /\ pc = "L2"
      /\ /\ out1' = r1
         /\ out2' = r2
      /\ pc' = "Done"
      /\ UNCHANGED << l1, l2, next1, next2, n1, n2, c1, c2, x1, x2, r1, r2, 
                      v_eps, v_delta >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == L1 \/ L2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


=============================================================================
