import Lemma.Bool.Eq.of.SEq
import Lemma.Bool.EqCast.of.Eq
import Lemma.Bool.SEq.of.SEq.SEq
import Lemma.Bool.HEq.of.Eq_Cast
open Bool


@[main]
private lemma main
  {a : List.Vector α n}
  {b : List.Vector α n'}
-- given
  (h₀ : n = n')
  (h₁ : b = cast (by rw [h₀]) a) :
-- imply
  b ≃ a := by
-- proof
  constructor
  .
    simp_all
  .
    apply HEq.of.Eq_Cast h₁


-- created on 2025-07-07
