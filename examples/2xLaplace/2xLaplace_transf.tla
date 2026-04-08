------------------------------ MODULE 2xLaplace_transf ------------------------------
EXTENDS Integers, DP

CONSTANT Epsilon

(*--algorithm 2xLaplace {
    variables
    (* inputs *)
    mem1 \in [a: Value, b: Value], mem2 \in [a: Value, b: Value],
    (* registers *)
    y1 = 0, y2 = 0,
    z1 = 0, z2 = 0,
    (* return register *)
    out1 = <<0, 0>>, out2 = <<0, 0>>,
    (* Privacy cost variables *)
    v_eps = 0,
    v_delta = 0;
  {
    L1: with (res \in AbsLap(Epsilon, mem1.a, mem2.a, v_eps, v_delta)) {
          y1 := res[1] || y2 := res[2] || v_eps := res[3] || v_delta := res[4]
        }; 
    L2: with (res \in AbsLap(Epsilon, mem1.b, mem2.b, v_eps, v_delta)) {
          z1 := res[1] || z2 := res[2] || v_eps := res[3] || v_delta := res[4]
        };
    L3: out1 := <<y1, z1>> || out2 := <<y2, z2>>; 
  }
} *)
\* BEGIN TRANSLATION (chksum(pcal) = "89f08ab4" /\ chksum(tla) = "3e974634")
VARIABLES pc, mem1, mem2, y1, y2, z1, z2, out1, out2, v_eps, v_delta

vars == << pc, mem1, mem2, y1, y2, z1, z2, out1, out2, v_eps, v_delta >>

Init == (* Global variables *)
        /\ mem1 \in [a: Value, b: Value]
        /\ mem2 \in [a: Value, b: Value]
        /\ y1 = 0
        /\ y2 = 0
        /\ z1 = 0
        /\ z2 = 0
        /\ out1 = <<0, 0>>
        /\ out2 = <<0, 0>>
        /\ v_eps = 0
        /\ v_delta = 0
        /\ pc = "L1"

L1 == /\ pc = "L1"
      /\ \E res \in AbsLap(Epsilon, mem1.a, mem2.a, v_eps, v_delta):
           /\ v_delta' = res[4]
           /\ v_eps' = res[3]
           /\ y1' = res[1]
           /\ y2' = res[2]
      /\ pc' = "L2"
      /\ UNCHANGED << mem1, mem2, z1, z2, out1, out2 >>

L2 == /\ pc = "L2"
      /\ \E res \in AbsLap(Epsilon, mem1.b, mem2.b, v_eps, v_delta):
           /\ v_delta' = res[4]
           /\ v_eps' = res[3]
           /\ z1' = res[1]
           /\ z2' = res[2]
      /\ pc' = "L3"
      /\ UNCHANGED << mem1, mem2, y1, y2, out1, out2 >>

L3 == /\ pc = "L3"
      /\ /\ out1' = <<y1, z1>>
         /\ out2' = <<y2, z2>>
      /\ pc' = "Done"
      /\ UNCHANGED << mem1, mem2, y1, y2, z1, z2, v_eps, v_delta >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == L1 \/ L2 \/ L3
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
