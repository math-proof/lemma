import sympy.concrete.expr_with_limits
import Mathlib.Algebra.Order.Floor.Ring
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ} :
-- imply
  ⌊x⌋ = (Maxima {n : ℤ | (n : ℝ) ≤ x} (fun n => n) : ℤ) := by
-- proof
  rw [Maxima, Set.image_id']
  exact (IsGreatest.csSup_eq (s := {n : ℤ | (n : ℝ) ≤ x}) ⟨Int.floor_le x, fun n (hn : (n : ℝ) ≤ x) => Int.le_floor.mpr hn⟩).symm


-- created on 2026-09-27
