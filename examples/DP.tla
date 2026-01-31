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

(******************)
(* Nats are reals *)
(******************)
LEMMA NatsAreReals == Nat \in SUBSET Real

(****************************************************************)
(* Placeholder for neglog, should be defined for positive reals *)
(****************************************************************)
NegLog == CHOOSE f : f \in [{r \in Real : r > 0} -> Real]

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
(****************************************************************************)

CONSTANTS
  Lap(_),     (* Laplace: Value ->^R Value *)
  Exp(_, _),  (* Exponential: Score x Value ->^R Value *)
  Value

(**********************************************************************)
(* Abstract procedures for DP mechanisms, à la [Barthe et al., 2014]. *)
(**********************************************************************)
CONSTANTS
  AbsLap(_, _, _, _),       (* v1, v2, v_eps, v_delta -> (x1, x2, v_eps', v_delta') *)
  AbsExp(_, _, _, _, _, _)  (* s1, v1, s2, v2, v_eps, v_delta -> (x1, x2, v_eps', v_delta') *)

CONSTANTS
  Epsilon, (* Privacy budget parameter *)
  Delta    (* Failure tolerance parameter *)

(*****************************************************************************)
(* Set of value pairs and updated ghost variable values corresponding to the *)
(* Hoare specification of the abstract Laplace mechanism procedure.          *)
(*****************************************************************************)
AbsLapHoareSpec(x1, x2, v_eps, v_delta) == 
  LET new_eps == v_eps + Epsilon * AbsVal(x1 - x2) IN
  {<<n, n, new_eps, v_delta>> : n \in Value}
    
(***********************************************)
(* Same definition as an assumption on AbsLap. *)
(***********************************************)
LEMMA AbsLapHoareSpecDef ==
  \A x1, x2 \in Value :
    \A v_eps, v_delta \in Real :  
      AbsLap(x1, x2, v_eps, v_delta) = AbsLapHoareSpec(x1, x2, v_eps, v_delta)

(*****************************************************************************)
(* Set of value pairs and updated ghost variable values corresponding to the *)
(* accuracy specification of the abstract Laplace mechanism procedure.       *)
(*****************************************************************************)
AbsLapAccSpec(x1, x2, v_eps, v_delta) == 
  IF 
    x1 = x2 (* pre-condition *)
  THEN
    LET new_delta == v_delta + Delta IN
    {<<n, n, v_eps, new_delta>> : 
      (* Note the accuracy guarantee in the post-condition *)
      n \in {m \in Value : Epsilon * AbsVal(m - x1) <= NegLog[Delta]}} 
  ELSE
    {}

(***********************************************)
(* Same definition as an assumption on AbsLap. *)
(***********************************************)
LEMMA AbsLapAccSpecDef ==
  \A x1, x2 \in Value :
    \A v_eps, v_delta \in Real :
      x1 = x2 =>
      AbsLap(x1, x2, v_eps, v_delta) = AbsLapAccSpec(x1, x2, v_eps, v_delta)

(*****************************************************************************)
(* Set of value pairs and updated ghost variable values corresponding to the *)
(* Hoare specification of the abstract Exponential mechanism procedure.      *)
(*****************************************************************************)
AbsExpHoareSpec(s1, v1, s2, v2, v_eps, v_delta) == 
  LET score_diff_set == {AbsVal(s1[v1, r] - s2[v2, r]) : r \in Value} IN
  LET new_eps == v_eps + Epsilon * Max(score_diff_set) IN
  {<<n, n, new_eps, v_delta>> : n \in Value}
    
(***********************************************)
(* Same definition as an assumption on AbsExp. *)
(***********************************************)
LEMMA AbsExpHoareSpecDef ==
  \A v1, v2 \in Value : 
    \A v_eps, v_delta \in Real :
      \A s1, s2 \in [Value \X Value -> Real] :
        AbsExp(s1, v1, s2, v2, v_eps, v_delta) = 
        AbsExpHoareSpec(s1, v1, s2, v2, v_eps, v_delta)

=============================================================================