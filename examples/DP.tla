--------------------------------- MODULE DP ---------------------------------
LOCAL INSTANCE Integers

-----------------------------------------------------------------------------
(* Math *)

(* Absolute value *)
AbsVal(x) == IF x < 0 THEN -x ELSE x

(* Max *)
Max(S) == CHOOSE m \in S : \A s \in S : s <= m

(* Placeholder *)
Real == {}

(* 0 is real *)
ASSUMPTION ZeroIsReal == 0 \in Real

(* Neglog *)
NegLog == CHOOSE f \in [{r \in Real : r > 0} -> Real] : TRUE

-----------------------------------------------------------------------------

(* Laplace & exponential assignment *)
CONSTANTS
  Lap(_)   (*  value ->^R value *)
  \*   Exp(_, _) (* score, value ->^R value *)

(* Abstract Laplace & exponential invocation *)
CONSTANTS
  AbsLap(_, _, _, _)       (* v1, v2, v_eps, v_delta -> (x1, x2, v_eps', v_delta') *)
  \*   AbsExp(_, _, _, _, _, _)  (* s1, v1, s2, v2, v_eps, v_delta -> (x1, x2, v_eps', v_delta') *)

CONSTANTS
  Epsilon,
  Delta

(* Assumption of Hoare specification for abstract Laplace invocation *)
(* For integers *)
ASSUMPTION AbsLapHoareSpecForInts ==
  \A x1, x2, v_eps, v_delta \in Int :
    \A res \in AbsLap(x1, x2, v_eps, v_delta) :
       /\ res \in Int \X Int \X Int \X Int
       /\ res[1] = res[2]
       /\ res[3] = v_eps + Epsilon * AbsVal(x1 - x2)
       /\ res[4] = v_delta

ASSUMPTION AbsLapHoareSpecForReals ==
  \A x1, x2, v_eps, v_delta \in Real :
    \A res \in AbsLap(x1, x2, v_eps, v_delta) :
       /\ res \in Real \X Real \X Real \X Real
       /\ res[1] = res[2]
       /\ res[3] = v_eps + Epsilon * AbsVal(x1 - x2)
       /\ res[4] = v_delta

ASSUMPTION AbsLapAccSpecForReals ==
  \A x1, x2, v_eps, v_delta \in Real :
    x1 = x2 =>
    \A res \in AbsLap(x1, x2, v_eps, v_delta) :
       /\ res \in Real \X Real \X Real \X Real
       /\ res[1] = res[2]
       /\ Epsilon * AbsVal(res[1] - x1) <= NegLog[Delta]
       /\ res[3] = v_eps
       /\ res[4] = v_delta + Delta

\* ASSUMPTION AbsLapAccSpecForInts ==
\*   \A eps, x1, x2, v_eps, v_delta \in Int :
\*     x1 = x2 =>
\*     \A res \in AbsLap(x1, x2, v_eps, v_delta) :
\*        /\ res \in Int \X Int \X Int \X Int
\*        /\ res[1] = res[2]
\*        /\ eps * AbsVal(res[1] - x1) <= InvLog(v_delta)
\*        /\ res[3] = v_eps
\*        /\ res[4] = v_delta + Delta

\* ASSUMPTION AbsExpHoareSpecForInts == 
\*   \A v1, v2, v_eps, v_delta \in Int :
\*     \A s1, s2 \in [Int \X Int -> Int] : s1 = s2 =>
\*        \A res \in AbsExp(s1, v1, s2, v2, v_eps, v_delta) :
\*           /\ res \in Int \X Int \X Int \X Int
\*           /\ res[1] = res[2]
\*           /\ LET abs_diff_set == {AbsVal(s1[v1, r] - s2[v2, r]) : r \in Int} IN
\*              res[3] = v_eps + Epsilon * Max(abs_diff_set)
\*           /\ res[4] = v_delta

=============================================================================