import sympy.vector.vector
import Lemma.Logic.EqUFnS.of.Eq
import Lemma.List.LengthFlatten.eq.SumMapLength
import Lemma.List.MapMap.eq.Map_Comp
open Logic List


@[main]
private lemma main
  {a b : List (List.Vector α n)}
-- given
  (h₀ : n > 0)
  (h₁ : (a.map List.Vector.toList).flatten = (b.map List.Vector.toList).flatten) :
-- imply
  a.length = b.length := by
-- proof
  have h_length := EqUFnS.of.Eq h₁ List.length
  repeat rw [LengthFlatten.eq.SumMapLength, MapMap.eq.Map_Comp] at h_length
  have h_comp : (List.length ∘ List.Vector.toList : List.Vector α n → ℕ) = (List.Vector.length : List.Vector α n → ℕ) := by
    ext x
    simp [List.Vector.toList]
  simp [h_comp] at h_length
  obtain h_Or | h_Eq_0 := h_length
  ·
    assumption
  ·
    rw [h_Eq_0] at h₀
    contradiction


-- created on 2025-05-11
