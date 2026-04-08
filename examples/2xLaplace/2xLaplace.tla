------------------------------ MODULE 2xLaplace ------------------------------
EXTENDS Integers, DP

CONSTANT Epsilon

(*--algorithm 2xLaplace {
  variables 
    (* inputs *)
    mem \in [a: Value, b: Value],
    (* registers *)
    y = 0,
    z = 0,
    (* return register *) 
    out = <<0, 0>>;
  {
    L1: y := Lap(Epsilon, mem.a); 
    L2: z := Lap(Epsilon, mem.b);
    L3: out := <<y, z>>; 
  }
} *)

=============================================================================
