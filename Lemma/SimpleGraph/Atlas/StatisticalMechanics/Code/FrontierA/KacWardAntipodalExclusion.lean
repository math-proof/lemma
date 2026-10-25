import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAntipodalExclusion
open StatMech StatMech.FrontierA


/--
[kw_angle_diagonal_ne_pi_of_no_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAntipodalExclusion.lean)
-/
@[path]
private lemma kw_angle_diagonal_ne_pi_of_no_between_eq
  {P A C : ℂ}
-- given
  (hPA : P ≠ A)
  (hAC : A ≠ C)
  (hPC : P ≠ C)
  (hPnot : ¬Sbtw ℝ A P C)
  (hCnot : ¬Sbtw ℝ P C A) :
-- imply
  (Complex.arg (C - A) : Real.Angle) - (Complex.arg (A - P) : Real.Angle) ≠ (Real.pi : Real.Angle) := by
-- proof
  apply StatMech.FrontierA.kw_angle_diagonal_ne_pi_of_no_between hPA hAC hPC hPnot hCnot


-- created on 2026-10-23
