import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripIdentity.Part2
open StatMech StatMech.Universality


/--
[hexCS_startReturnLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripIdentity.lean)
-/
@[path]
private lemma hexCS_startReturnLaw_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  HexCSStartReturnLaw T L hT := by
-- proof
  apply StatMech.Universality.hexCS_startReturnLaw T L hT

/--
[hexCSCanonicalWindingLaw_of_exit_window](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripIdentity.lean)
-/
@[path]
private lemma hexCSCanonicalWindingLaw_of_exit_window_eq
  {T L : ℕ}
  {hT : 0 < T}
-- given
  (hexit : HexCSBoundaryExitLaw T L hT)
  (hwindow : HexCSBoundaryWindowLaw T L hT) :
-- imply
  HexCSCanonicalWindingLaw T L hT := by
-- proof
  apply StatMech.Universality.hexCSCanonicalWindingLaw_of_exit_window hexit hwindow

/--
[hexCS_finite_strip_identity_of_exit_window](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripIdentity.lean)
-/
@[path]
private lemma hexCS_finite_strip_identity_of_exit_window_eq
  {T L : ℕ}
-- given
  (hT : 0 < T)
  (hlocal : HexCSLocalRelation T L hT)
  (hexit : HexCSBoundaryExitLaw T L hT)
  (hwindow : HexCSBoundaryWindowLaw T L hT) :
-- imply
  hexCl * hexCSA T L hT + hexCt * hexCSE T L hT + hexCSB T L hT = 1 := by
-- proof
  apply StatMech.Universality.hexCS_finite_strip_identity_of_exit_window T L hT hlocal hexit hwindow

/--
[hexCS_boundary_masses_nonneg_of_exit_window](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripIdentity.lean)
-/
@[path]
private lemma hexCS_boundary_masses_nonneg_of_exit_window_eq
  {T L : ℕ}
-- given
  (hT : 0 < T)
  (hlocal : HexCSLocalRelation T L hT)
  (hexit : HexCSBoundaryExitLaw T L hT)
  (hwindow : HexCSBoundaryWindowLaw T L hT) :
-- imply
  0 ≤ hexCSA T L hT ∧ 0 ≤ hexCSE T L hT ∧ 0 ≤ hexCSB T L hT := by
-- proof
  apply StatMech.Universality.hexCS_boundary_masses_nonneg_of_exit_window T L hT hlocal hexit hwindow


-- created on 2026-10-23
