import Lemma.Logic.Eq.of.SEq
import Lemma.Logic.EqCast.of.Eq
import Lemma.Logic.SEq.of.SEq.SEq
import Lemma.Logic.HEq.of.Eq_Cast
open Logic


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
