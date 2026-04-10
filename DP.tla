--------------------------------- MODULE DP ---------------------------------
LOCAL INSTANCE Integers

-----------------------------------------------------------------------------
(********)
(* Math *)
(********)

(******************)
(* Absolute value *)
(******************)
AbsVal(x) == IF x < 0 THEN -x ELSE x

(*******)
(* Max *)
(*******)
Max(S) == CHOOSE m \in S : \A s \in S : s <= m

(*************************)
(* Placeholder for reals *)
(*************************)
Real == Int

(*************)
(* 0 is real *)
(*************)
LEMMA ZeroIsReal == 0 \in Real

(****************************************************************************)
(* Opaque tail bound for the discrete Laplace distribution w/ parameter eps *)
(*   LapTail[eps, T] = 2 * exp(-eps * T)                                    *)
(* By the discrete Laplace tail bound,                                      *)
(*   Pr_{v ~ Lap_eps(a)}[|v - a| > T] <= LapTail[eps, T]                    *)
(* for any center a, parameter eps > 0, and integer T >= 1.                 *)
(****************************************************************************)
LapTail == CHOOSE f : 
  f \in [{e \in Real : e > 0} \X Nat -> {r \in Real : r >= 0}]

LEMMA LapTailType ==
  \A eps \in Real : eps >= 0 =>
    \A t \in Nat : /\ LapTail[eps, t] \in Real
                   /\ 0 <= LapTail[eps, t]

-----------------------------------------------------------------------------
(********************************)
(* DP primitives and parameters *)
(********************************)

(****************************************************************************)
(* Laplace mechanism and exponential mechanism                              *)
(* -------------------------------------------                              *)
(* These are normally probabilistic assignments.                            *)
(* In this project, they are left as undefined constants that get replaced  *)
(* during the conversion to self-product programs by invocations to the     *)
(* abstract procedures defined below.                                       *)
(*                                                                          *)
(* Each mechanism takes its privacy parameter (eps) as first argument.      *)
(****************************************************************************)

CONSTANTS
  Lap(_, _),      (* eps x Value ->^R Value *)
  Exp(_, _, _),   (* eps x Score x Value ->^R Value *)
  Value

(**********************************************************************)
(* Abstract procedures for DP mechanisms, à la [Barthe et al., 2014]. *)
(* Each takes the per-call privacy parameter eps as first argument.   *)
(**********************************************************************)
CONSTANTS
  AbsLap(_, _, _, _, _),          (* eps, v1, v2, v_eps, v_delta *)
  AbsExp(_, _, _, _, _, _, _)     (* eps, s1, v1, s2, v2, v_eps, v_delta *)

(*****************************************************************************)
(* Hoare specification of the abstract Laplace mechanism procedure.          *)
(* Returns {<<n, n, v_eps + eps * |x1 - x2|, v_delta>> : n in Value}.        *)
(*****************************************************************************)
AbsLapHoareSpec(eps, x1, x2, v_eps, v_delta) == 
  LET new_eps == v_eps + eps * AbsVal(x1 - x2) IN
  {<<n, n, new_eps, v_delta>> : n \in Value}
    
LEMMA AbsLapHoareSpecDef ==
  \A eps \in Real :
    \A x1, x2 \in Value :
      \A v_eps, v_delta \in Real :  
        AbsLap(eps, x1, x2, v_eps, v_delta) = 
        AbsLapHoareSpec(eps, x1, x2, v_eps, v_delta)

(*****************************************************************************)
(* Accuracy specification of the abstract Laplace mechanism procedure.       *)
(* Requires x1 = x2 as precondition. Restricts output to values within T     *)
(* of x1 and increments v_delta by LapTail[eps, T].                          *)
(*****************************************************************************)
AbsLapAccSpec(eps, T, x1, x2, v_eps, v_delta) == 
  IF x1 = x2 THEN
    LET new_delta == v_delta + LapTail[eps, T] IN
    {<<n, n, v_eps, new_delta>> : 
      n \in {m \in Value : AbsVal(m - x1) <= T}} 
  ELSE {}

LEMMA AbsLapAccSpecDef ==
  \A eps \in Real : \A T \in Nat :
    \A x1, x2 \in Value :
      \A v_eps, v_delta \in Real :
        x1 = x2 =>
        AbsLap(eps, x1, x2, v_eps, v_delta) = 
        AbsLapAccSpec(eps, T, x1, x2, v_eps, v_delta)

(*****************************************************************************)
(* Hoare specification of the abstract Exponential mechanism procedure.      *)
(*****************************************************************************)
AbsExpHoareSpec(eps, s1, v1, s2, v2, v_eps, v_delta) == 
  LET score_diff_set == {AbsVal(s1[v1, r] - s2[v2, r]) : r \in Value} IN
  LET new_eps == v_eps + eps * Max(score_diff_set) IN
  {<<n, n, new_eps, v_delta>> : n \in Value}
    
LEMMA AbsExpHoareSpecDef ==
  \A eps \in Real :
    \A v1, v2 \in Value : 
      \A v_eps, v_delta \in Real :
        \A s1, s2 \in [Value \X Value -> Real] :
          AbsExp(eps, s1, v1, s2, v2, v_eps, v_delta) = 
          AbsExpHoareSpec(eps, s1, v1, s2, v2, v_eps, v_delta)

=============================================================================