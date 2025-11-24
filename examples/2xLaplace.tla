------------------------------ MODULE 2xLaplace ------------------------------
EXTENDS Integers, DP
CONSTANT Eps

(*--algorithm 2xLaplace {
  variables 
    (* inputs *)
    mem \in [a: Int, b: Int],
    (* registers *)
    y = 0,
    z = 0,
    (* return register *) 
    out = <<0, 0>>;
  {
    L1: y := Lap(Eps, mem.a); 
    L2: z := Lap(Eps, mem.b);
    L3: out := <<y, z>>; 
  }
} *)

=============================================================================
