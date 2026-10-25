import Mathlib
import sympy.Basic


/--
If `1 < ||u||`, then `u != 0`.
-/
@[path]
private lemma main
  [NontriviallyNormedField K]
  {u : K}
-- given
  (hu : 1 < ‖u‖) :
-- imply
  u ≠ 0 := by
-- proof
  intro h
  rw [h, norm_zero] at hu
  linarith


-- created on 2026-10-24
