import Lemma.Vector.EqGetCast_MapRange.of.Eq
open Vector


@[main]
private lemma main
-- given
  (h₀ : i < n)
  (h₁ : n = n')
  (f : Fin n → α) :
-- imply
  have h : List.Vector α n = List.Vector α n' := by rw [h₁]
  (cast h ((List.Vector.range n).map f))[i] = f ⟨i, h₀⟩ := by
-- proof
  have := EqGetCast_MapRange.of.Eq h₁ f ⟨i, h₀⟩
  simp_all


-- created on 2025-07-06
