import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : Fin n → ℝ} :
-- imply
  x ≤ fun _ => Real.log (∑ j, Real.exp (x j)) := by
-- proof
  intro i
  calc
    x i = Real.log (Real.exp (x i)) := (Real.log_exp (x i)).symm
    _ ≤ Real.log (∑ j, Real.exp (x j)) :=
      Real.log_le_log (Real.exp_pos (x i)) (Finset.single_le_sum (fun j _ => (Real.exp_pos (x j)).le) (Finset.mem_univ i))


-- created on 2026-09-27
