import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricDensityJacobian.Part4
open Finset Matrix StatMech StatMech.FrontierD


/--
[sixVertexOddSymmetricLift_positive_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricDensityJacobian.lean)
-/
@[path]
private lemma sixVertexOddSymmetricLift_positive_mem_Icc_eq
  {m : Nat}
  {q : Fin m → Real}
  {j : Fin m}
-- given
  (hq : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q)) :
-- imply
  q j ∈ Set.Icc 0 Real.pi := by
-- proof
  apply StatMech.FrontierD.sixVertexOddSymmetricLift_positive_mem_Icc hq j

/--
[sixVertexOddPositiveHalfRootGap_pos_of_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricDensityJacobian.lean)
-/
@[path]
private lemma sixVertexOddPositiveHalfRootGap_pos_of_open_eq
  {m : Nat}
  {q : Fin m → Real}
  {k : Fin m}
-- given
  (hq : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q)) :
-- imply
  0 < sixVertexOddPositiveHalfRootGap q k := by
-- proof
  apply StatMech.FrontierD.sixVertexOddPositiveHalfRootGap_pos_of_open hq k

/--
[sixVertexOddPositiveHalfCellLeftIndex_val_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricDensityJacobian.lean)
-/
@[path]
private lemma sixVertexOddPositiveHalfCellLeftIndex_val_add_one_eq
  {m : Nat}
  {j : Fin m} :
-- imply
  (sixVertexOddPositiveHalfCellLeftIndex j).val + 1 = (sixVertexOddPositiveIndex m j).val := by
-- proof
  apply StatMech.FrontierD.sixVertexOddPositiveHalfCellLeftIndex_val_add_one j

/--
[sixVertexOddSymmetricLift_positiveHalfCellLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricDensityJacobian.lean)
-/
@[path]
private lemma sixVertexOddSymmetricLift_positiveHalfCellLeft_eq
  {m : Nat}
  {q : Fin m → Real}
  {j : Fin m} :
-- imply
  sixVertexOddSymmetricLift m q (sixVertexOddPositiveHalfCellLeftIndex j) = q j - sixVertexOddPositiveHalfRootGap q j := by
-- proof
  apply StatMech.FrontierD.sixVertexOddSymmetricLift_positiveHalfCellLeft q j

/--
[sixVertexCentralQuantumNumber_oddPositiveHalfCell_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricDensityJacobian.lean)
-/
@[path]
private lemma sixVertexCentralQuantumNumber_oddPositiveHalfCell_sub_eq
  {m : Nat}
  {j : Fin m} :
-- imply
  sixVertexCentralQuantumNumber (sixVertexOddPositiveIndex m j) - sixVertexCentralQuantumNumber (sixVertexOddPositiveHalfCellLeftIndex j) = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexCentralQuantumNumber_oddPositiveHalfCell_sub j

/--
[intervalIntegral_sixVertexFiniteRootDensity_oddPositiveHalfCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricDensityJacobian.lean)
-/
@[path]
private lemma intervalIntegral_sixVertexFiniteRootDensity_oddPositiveHalfCell_eq
  {c : Real}
  {N m : Nat}
  {q : Fin m → Real}
  {j : Fin m}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hsol : SixVertexSatisfiesBetheEquations c N ((m + 1) + m) (sixVertexOddSymmetricLift m q)) :
-- imply
  ∫ x in q j - sixVertexOddPositiveHalfRootGap q j..q j, sixVertexFiniteRootDensity c N ((m + 1) + m) (sixVertexOddSymmetricLift m q) x = 1 / N := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_sixVertexFiniteRootDensity_oddPositiveHalfCell hc hN hsol j

/--
[sixVertexOddPositiveHalfRootGap_upper_of_finiteDensityLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricDensityJacobian.lean)
-/
@[path]
private lemma sixVertexOddPositiveHalfRootGap_upper_of_finiteDensityLower_eq
  {c : Real}
  {N m : Nat}
  {q : Fin m → Real}
  {lower : Real}
  {j : Fin m}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hopen : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q))
  (hsol : SixVertexSatisfiesBetheEquations c N ((m + 1) + m) (sixVertexOddSymmetricLift m q))
  (hlower : 0 < lower)
  (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N ((m + 1) + m) (sixVertexOddSymmetricLift m q) x) :
-- imply
  sixVertexOddPositiveHalfRootGap q j ≤ 1 / ((N : Real) * lower) := by
-- proof
  apply StatMech.FrontierD.sixVertexOddPositiveHalfRootGap_upper_of_finiteDensityLower hc hN hopen hsol hlower hdensity j

/--
[sixVertexBetheOddPositiveHalfJacobianMatrix_diag_eq_finiteRootDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricDensityJacobian.lean)
-/
@[path]
private lemma sixVertexBetheOddPositiveHalfJacobianMatrix_diag_eq_finiteRootDensity_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real}
  {j : Fin m}
-- given
  (hN : 0 < N) :
-- imply
  sixVertexBetheOddPositiveHalfJacobianMatrix N m c q j j = 2 * Real.pi * N * sixVertexFiniteRootDensity c N ((m + 1) + m) (sixVertexOddSymmetricLift m q) (q j) - sixVertexBetheOddSymmetricJacobianCorrection c m q j := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheOddPositiveHalfJacobianMatrix_diag_eq_finiteRootDensity hN q j

/--
[norm_sixVertexBetheOddSymmetricJacobianCorrection_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricDensityJacobian.lean)
-/
@[path]
private lemma norm_sixVertexBetheOddSymmetricJacobianCorrection_le_eq
  {c : Real}
  {m : Nat}
  {q : Fin m → Real}
  {j : Fin m}
-- given
  (hc : 2 < c) :
-- imply
  ‖sixVertexBetheOddSymmetricJacobianCorrection c m q j‖ ≤ 2 * (sixVertexAnisotropyMagnitude c / (sixVertexAnisotropyMagnitude c - 1)) := by
-- proof
  apply StatMech.FrontierD.norm_sixVertexBetheOddSymmetricJacobianCorrection_le hc q j

/--
[abs_sixVertexBetheOddPositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricDensityJacobian.lean)
-/
@[path]
private lemma abs_sixVertexBetheOddPositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real}
  {j : Fin m}
  {E mesh : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hgap : 0 ≤ sixVertexOddPositiveHalfRootGap q j)
  (hmesh : sixVertexOddPositiveHalfRootGap q j ≤ mesh)
  (hcell : |sixVertexOddPositiveHalfRootGap q j * sixVertexFiniteRootDensity c N ((m + 1) + m) (sixVertexOddSymmetricLift m q) (q j) - 1 / N| ≤ E) :
-- imply
  |sixVertexBetheOddPositiveHalfScaledJacobianMatrix N m c q j j - 2 * Real.pi| ≤ 2 * Real.pi * N * E + 2 * (sixVertexAnisotropyMagnitude c / (sixVertexAnisotropyMagnitude c - 1)) * mesh := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexBetheOddPositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le hc hN hgap hmesh hcell


-- created on 2026-10-23
