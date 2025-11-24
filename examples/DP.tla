--------------------------------- MODULE DP ---------------------------------
(* Laplace & exponential assignment *)
CONSTANTS
  Lap(_, _),   (* epsilon, value ->^R value *)
  Exp(_, _, _) (* epsilon, score, value ->^R value *)

(* Abstract Laplace & exponential invocation *)
CONSTANTS
  AbsLap(_, _, _, _, _),       (* epsilon, v1, v2, v_eps, v_delta -> (x1, x2, v_eps', v_delta') *)
  AbsExp(_, _, _, _, _, _, _)  (* epsilon, s1, v1, s2, v2, v_eps, v_delta -> (x1, x2, v_eps', v_delta') *)

=============================================================================