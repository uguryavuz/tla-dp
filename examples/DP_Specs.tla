------------------------------- MODULE DP_Specs ------------------------------
LOCAL INSTANCE Integers

(* Absolute value *)
AbsVal(x) == IF x < 0 THEN -x ELSE x

(* Hoare specification of abstract Laplace procedure *)
AbsLapSpec(epsilon, v1, v2, v_eps, v_delta) ==
  LET new_budget == v_eps + epsilon * AbsVal(v1 - v2) IN
  {<<n, n, new_budget, v_delta>> : n \in Int}

(* Max *)
Max(S) == CHOOSE m \in S : \A s \in S : s <= m

(* Hoare specification of abstract exponential procedure *)
AbsExpSpec(epsilon, s1, v1, s2, v2, v_eps, v_delta) ==
  IF s1 # s2 
    THEN {} 
    ELSE
      LET abs_diff_set(sc1, e1, sc2, e2) == 
          {AbsVal(sc1[e1, r] - sc2[e2, r]) : r \in Int} IN
      LET new_budget == 
          v_eps + epsilon * Max(abs_diff_set(s1, v1, s2, v2)) IN
      {<<n, n, new_budget, v_delta>> : n \in Int}

=============================================================================