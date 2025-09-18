import stdlib.SEq
import Lemma.Algebra.Val.eq.Nil.of.EqLength_0
import Lemma.Algebra.HEq.of.EqValS
open Algebra


@[main]
private lemma main
  {a : List.Vector α n}
  {b : List.Vector α m}
-- given
  (h₀ : a.length = 0)
  (h₁ : b.length = 0) :
-- imply
  a ≃ b := by
-- proof
  simp [SEq]
  have h_a := Val.eq.Nil.of.EqLength_0 h₀
  have h_b := Val.eq.Nil.of.EqLength_0 h₁
  simp_all
  apply HEq.of.EqValS
  simp_all


-- created on 2025-05-29
