import Lemma.Vector.EqGetMapRange.of.Lt
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Vector.SEqArraySliceS.of.SEq.Eq.Eq
import Theorem.Nat.EqMin.of.Le
import Theorem.Nat.Le_SubMulS.of.Lt
open Vector Bool Nat


@[path]
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
  subst h₀ h₁ h₃
  unfold List.Vector.unflatten
  repeat rw [EqGetMapRange.of.Lt h₂]
  simp
  apply SEqCastS.of.SEq.Eq.Eq
  repeat {
    rw [EqMin.of.Le]
    apply Le_SubMulS.of.Lt
    simp_all
  }
  ·
    apply SEqArraySliceS.of.SEq.Eq.Eq
    all_goals first | rfl | apply h₄


-- created on 2025-07-15
-- updated on 2026-11-20
