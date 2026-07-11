import Lemma.Bool.SEqBFnS.of.SEq.SEq
import sympy.vector.vector
open Bool


@[main]
private lemma main
  [Mul α]
  {a b : List.Vector α n}
  {a' b' : List.Vector α n'}
-- given
  (h_a : a ≃ a')
  (h_b : b ≃ b') :
-- imply
  a * b ≃ a' * b' :=
-- proof
  SEqBFnS.of.SEq.SEq h_a h_b (· * ·)


-- created on 2026-07-11
