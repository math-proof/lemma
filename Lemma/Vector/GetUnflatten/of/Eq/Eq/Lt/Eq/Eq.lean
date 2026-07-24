import Lemma.Vector.EqGetMapRange.of.Lt
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Vector.SEqArraySliceS.of.SEq.Eq.Eq
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.Le_SubMulS.of.Lt
open Vector Bool Nat


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
    apply SEqArraySliceS.of.SEq.Eq.Eq
    repeat simp_all


-- created on 2025-07-15
