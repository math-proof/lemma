import Lemma.Nat.Sub.ge.One.of.Gt
open Nat


@[path]
private lemma main
  [IntegerRing Z]
  {a b : Z}
-- given
  (h : a < b) :
-- imply
  b - a ≥ 1 := 
-- proof
  Sub.ge.One.of.Gt h


-- created on 2025-05-18
-- updated on 2025-06-21
