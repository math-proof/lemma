import Def.Data.Vector.Basic
import Theorem.Logic.SEq
import Instance.Data.Vector.Vector


@[path]
private lemma main
  {v : List.Vector α n}
  {v' : List.Vector α n'}
  {i s i' s' : ℕ}
-- given
  (h₀ : i = i')
  (h₁ : s = s')
  (h₂ : v ≃ v') :
-- imply
  v.array_slice i s ≃ v'.array_slice i' s' := by
-- proof
  subst h₀ h₁
  simp [SEq] at h₂ ⊢
  aesop


-- created on 2025-05-31
-- updated on 2026-11-20
