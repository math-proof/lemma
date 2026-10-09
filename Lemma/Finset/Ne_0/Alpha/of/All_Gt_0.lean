import sympy.concrete.continued_fraction
import sympy.sets.sets
import sympy.Basic
import Lemma.Finset.All_Imp_GtAlpha_0
open Finset Continuant


@[path]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : n > 0)
  (h : ∀ i < n, x i > 0) :
-- imply
  alpha ((List.range n).map x) ≠ 0 := by
-- proof
  apply ne_of_gt
  apply All_Imp_GtAlpha_0
  · rw [Ne, List.map_eq_nil_iff, List.range_eq_nil]
    omega
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    exact h i (List.mem_range.mp hi)


@[path]
private lemma offset
  {n a b : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : a < n)
  (h : ∀ i, a ≤ i → i < n → x (i + b) > 0) :
-- imply
  alpha ((List.range (n - a)).map fun i => x (i + (a + b))) ≠ 0 := by
-- proof
  apply ne_of_gt
  apply All_Imp_GtAlpha_0
  · rw [Ne, List.map_eq_nil_iff, List.range_eq_nil]
    omega
  · intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
    have hi' := List.mem_range.mp hi
    have := h (i + a) (by omega) (by omega)
    rwa [show i + a + b = i + (a + b) by ring] at this


-- created on 2020-09-22
