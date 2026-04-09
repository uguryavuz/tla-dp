----------------------------- MODULE SmartSum_MC -----------------------------
EXTENDS SmartSum_transf

(********************************************************************)
(* Notion of adjacency between initial memories:                    *)
(* both input sequences differ in at most one element by at most 1. *)
(********************************************************************)
Phi(lv1, lv2) == 
  /\ Len(lv1) = Len(lv2)
  /\ Len(lv1) # 0 => \E i \in 1..Len(lv1) : 
                        /\ AbsVal(lv1[i] - lv2[i]) <= 1
                        /\ \A j \in 1..Len(lv1) : j # i => lv1[j] = lv2[j]

PhiSpec ==
  /\ Spec
  /\ Phi(l1, l2)

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

(**********************************************************)
(* Introduce bound on sequence lengths for model checking *)
(**********************************************************)
SeqLimit == 4
BoundedSeq(S) == UNION {[1..n -> S] : n \in 0..SeqLimit}

(***********************)
(* Set Q to a constant *)
(***********************)
QValue == 2

EpsConst == 1
BoundedInts == -2..2

===============================================================================
