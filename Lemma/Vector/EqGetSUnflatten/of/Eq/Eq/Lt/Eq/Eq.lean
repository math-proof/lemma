import Lemma.Vector.EqGetMapRange.of.Lt
import Lemma.Logic.SEqCastS.of.SEq.Eq.Eq
import Lemma.Vector.EqArraySliceS.of.SEq.Eq.Eq
import Lemma.Algebra.EqMin.of.Le
import Lemma.Algebra.Le_SubMulS.of.Lt
open Algebra Logic Vector


@[main]
private lemma main
  {v : List.Vector α (m * n)}
  {v' : List.Vector α (m' * n')}
  {i i' : ℕ}
-- given
  (h₀ : m = m')
  (h₁ : n = n')
  (h₂ : i < m)
  (h₃ : i = i')
  (h₄ : v ≃ v') :
-- imply
  v.unflatten[i] ≃ v'.unflatten[i'] := by
-- proof
  unfold List.Vector.unflatten
  repeat rw [EqGetMapRange.of.Lt (by simp_all)]
  simp
  apply SEqCastS.of.SEq.Eq.Eq
  repeat {
    rw [EqMin.of.Le]
    apply Le_SubMulS.of.Lt
    simp_all
  }
  ·
    apply EqArraySliceS.of.SEq.Eq.Eq
    repeat simp_all


-- created on 2025-07-15
