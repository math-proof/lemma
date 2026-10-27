import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricDensityJacobian
open Finset Matrix StatMech StatMech.FrontierD


/--
[sixVertexBethePositiveHalfJacobianMatrix_diag_eq_finiteRootDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricDensityJacobian.lean)
-/
@[path]
private lemma sixVertexBethePositiveHalfJacobianMatrix_diag_eq_finiteRootDensity_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real}
  {j : Fin m}
-- given
  (hN : 0 < N) :
-- imply
  sixVertexBethePositiveHalfJacobianMatrix N m c q j j = 2 * Real.pi * N * sixVertexFiniteRootDensity c N (m + m) (sixVertexEvenSymmetricLift m q) (q j) - sixVertexBetheSymmetricJacobianCorrection c m q j := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePositiveHalfJacobianMatrix_diag_eq_finiteRootDensity hN q j

/--
[norm_sixVertexBetheSymmetricJacobianCorrection_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricDensityJacobian.lean)
-/
@[path]
private lemma norm_sixVertexBetheSymmetricJacobianCorrection_le_eq
  {c : Real}
  {m : Nat}
  {q : Fin m → Real}
  {j : Fin m}
-- given
  (hc : 2 < c) :
-- imply
  ‖sixVertexBetheSymmetricJacobianCorrection c m q j‖ ≤ 2 * (sixVertexAnisotropyMagnitude c / (sixVertexAnisotropyMagnitude c - 1)) := by
-- proof
  apply StatMech.FrontierD.norm_sixVertexBetheSymmetricJacobianCorrection_le hc q j

/--
[abs_sixVertexBethePositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricDensityJacobian.lean)
-/
@[path]
private lemma abs_sixVertexBethePositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real}
  {j : Fin m}
  {E mesh : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hgap : 0 ≤ sixVertexPositiveHalfRootGap q j)
  (hmesh : sixVertexPositiveHalfRootGap q j ≤ mesh)
  (hcell : |sixVertexPositiveHalfRootGap q j * sixVertexFiniteRootDensity c N (m + m) (sixVertexEvenSymmetricLift m q) (q j) - 1 / N| ≤ E) :
-- imply
  |sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j j - 2 * Real.pi| ≤ 2 * Real.pi * N * E + 2 * (sixVertexAnisotropyMagnitude c / (sixVertexAnisotropyMagnitude c - 1)) * mesh := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexBethePositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le hc hN hgap hmesh hcell


-- created on 2026-10-23
