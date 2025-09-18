import Lemma.Algebra.EqGetCast_MapRange.of.Eq
open Algebra


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
  have h := EqGetCast_MapRange.of.Eq h₁ f (⟨i, h₀⟩ : Fin n)
  simp_all [h]


-- created on 2025-07-06
