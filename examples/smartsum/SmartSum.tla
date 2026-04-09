------------------------------ MODULE SmartSum ------------------------------
EXTENDS Integers, Sequences, DP

CONSTANTS Q, Epsilon

(*--algorithm SmartSum {
  variables 
    (* inputs *)
    l \in Seq(Value),
    (* registers *)
    next = 0,
    n = 0,
    c = 0,
    x = 0,
    r = <<>>,
    (* return register *)
    out = <<>>;
  {
    L1: while (0 < Len(l)) {
          if (Len(l) % Q = 1) {
            x := Lap(Epsilon, c + Head(l)); 
            n := x + n;
            next := n;
            c := 0;
            r := Append(r, next);
          } else {
            x := Lap(Epsilon, Head(l));
            next := next + x;
            c := c + Head(l);
            r := Append(r, next);
          }; 
          l := Tail(l);
        };
    L2: out := r; 
  }
} *)

=============================================================================
