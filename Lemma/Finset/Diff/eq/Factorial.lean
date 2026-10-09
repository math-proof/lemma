import sympy.core.function
import sympy.Basic
open Nat


@[path]
private lemma main
  {n : ℕ} :
-- imply
  Difference (fun x : ℝ => x ^ n) n = fun _ => (n ! : ℝ) := by
-- proof
  unfold Difference
  rw [fwdDiff_iter_eq_factorial]
  rfl


-- created on 2020-10-12
