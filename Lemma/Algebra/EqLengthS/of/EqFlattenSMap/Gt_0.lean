import stdlib.List.Vector
import Lemma.Logic.EqFunS.of.Eq
import Lemma.Algebra.LengthFlatten.eq.SumMapLength
import Lemma.Algebra.MapMap.eq.Map_Comp
open Logic Algebra


@[main]
private lemma main
  {a b : List (List.Vector α n)}
-- given
  (h₀ : n > 0)
  (h₁ : (a.map List.Vector.toList).flatten = (b.map List.Vector.toList).flatten) :
-- imply
  a.length = b.length := by
-- proof
  have h_length := EqFunS.of.Eq h₁ List.length
  rw [LengthFlatten.eq.SumMapLength, LengthFlatten.eq.SumMapLength] at h_length
  rw [MapMap.eq.Map_Comp, MapMap.eq.Map_Comp] at h_length
  have h_comp : (List.length ∘ List.Vector.toList : List.Vector α n → ℕ) = (List.Vector.length : List.Vector α n → ℕ) := by 
    ext x
    simp [List.Vector.toList]
  simp [h_comp] at h_length
  cases' h_length with h_Or h_Eq_0
  ·
    assumption
  ·
    rw [h_Eq_0] at h₀
    contradiction


-- created on 2025-05-11
