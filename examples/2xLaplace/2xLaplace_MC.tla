----------------------------- MODULE 2xLaplace_MC -----------------------------
EXTENDS 2xLaplace_transf

(*************************************************)
(* Notion of adjacency between initial memories: *)
(* both mem.a and mem.b differ by at most 1.     *)
(*************************************************)
Phi(m1, m2) ==
  /\ AbsVal(m1.a - m2.a) <= 1
  /\ AbsVal(m1.b - m2.b) <= 1

PhiSpec ==
  /\ Spec
  /\ Phi(mem1, mem2)

(***********************)
(* (2 * Epsilon, 0)-DP *)
(***********************)
DP ==
  pc = "Done" =>
    /\ out1 = out2
    /\ v_delta = 0
    /\ v_eps <= 2 * Epsilon

-------------------------------------------------------------------------------
(********************************)
(* Constants for model checking *)
(********************************)

EpsConst == 1
DelConst == 0
BoundedInts == -5..5

===============================================================================
