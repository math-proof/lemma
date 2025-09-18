import Lemma.Algebra.EqGetMapRange.of.Lt
import Lemma.Logic.EqCastS.of.Eq.Eq.Eq
import Lemma.Algebra.EqArraySliceS.of.Eq.Eq.Eq
import Lemma.Algebra.EqMin.of.Le
import Lemma.Algebra.Le_SubMulS.of.Lt
open Algebra Logic


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
  apply EqCastS.of.Eq.Eq.Eq
  repeat {
    rw [EqMin.of.Le]
    apply Le_SubMulS.of.Lt
    simp_all
  }
  ·
    apply EqArraySliceS.of.Eq.Eq.Eq
    repeat simp_all


-- created on 2025-07-15
