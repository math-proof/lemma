import sympy.concrete.expr_with_limits
import Mathlib.Algebra.Order.Floor.Ring
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  ⌈x⌉ = (Minima {n : ℤ | (n : ℝ) ≥ x} (fun n => n) : ℤ) := by
-- proof
  rw [Minima, Set.image_id']
  exact (IsLeast.csInf_eq (s := {n : ℤ | (n : ℝ) ≥ x}) ⟨Int.le_ceil x, fun n (hn : x ≤ (n : ℝ)) => Int.ceil_le.mpr hn⟩).symm


-- created on 2021-09-11
