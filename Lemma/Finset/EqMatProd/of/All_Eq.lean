import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n m : ℕ}
  {f g : ℕ → Matrix (Fin m) (Fin m) ℂ}
-- given
  (h : ∀ i < n, f i = g i) :
-- imply
  ((List.range n).map f).prod = ((List.range n).map g).prod := by
-- proof
  congr 1
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)


-- created on 2020-10-29
