import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricTailJacobian
open StatMech StatMech.FrontierD


/--
[sixVertexPositiveHalfCellLeftIndex_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricTailJacobian.lean)
-/
@[path]
private lemma sixVertexPositiveHalfCellLeftIndex_lt_eq
  {m : Nat}
  {j : Fin m} :
-- imply
  sixVertexPositiveHalfCellLeftIndex j < Fin.natAdd m j := by
-- proof
  apply StatMech.FrontierD.sixVertexPositiveHalfCellLeftIndex_lt j

/--
[sixVertexPositiveHalfCellLeftIndex_val_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricTailJacobian.lean)
-/
@[path]
private lemma sixVertexPositiveHalfCellLeftIndex_val_add_one_eq
  {m : Nat}
  {j : Fin m} :
-- imply
  (sixVertexPositiveHalfCellLeftIndex j).val + 1 = (Fin.natAdd m j).val := by
-- proof
  apply StatMech.FrontierD.sixVertexPositiveHalfCellLeftIndex_val_add_one j

/--
[sixVertexEvenSymmetricLift_positiveHalfCellLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricTailJacobian.lean)
-/
@[path]
private lemma sixVertexEvenSymmetricLift_positiveHalfCellLeft_eq
  {m : Nat}
  {q : Fin m → Real}
  {j : Fin m} :
-- imply
  sixVertexEvenSymmetricLift m q (sixVertexPositiveHalfCellLeftIndex j) = q j - sixVertexPositiveHalfRootGap q j := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenSymmetricLift_positiveHalfCellLeft q j

/--
[sixVertexCentralQuantumNumber_positiveHalfCell_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricTailJacobian.lean)
-/
@[path]
private lemma sixVertexCentralQuantumNumber_positiveHalfCell_sub_eq
  {m : Nat}
  {j : Fin m} :
-- imply
  sixVertexCentralQuantumNumber (Fin.natAdd m j) - sixVertexCentralQuantumNumber (sixVertexPositiveHalfCellLeftIndex j) = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexCentralQuantumNumber_positiveHalfCell_sub j

/--
[intervalIntegral_sixVertexFiniteRootDensity_positiveHalfCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricTailJacobian.lean)
-/
@[path]
private lemma intervalIntegral_sixVertexFiniteRootDensity_positiveHalfCell_eq
  {c : Real}
  {N m : Nat}
  {q : Fin m → Real}
  {j : Fin m}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hsol : SixVertexSatisfiesBetheEquations c N (m + m) (sixVertexEvenSymmetricLift m q)) :
-- imply
  ∫ x in q j - sixVertexPositiveHalfRootGap q j..q j, sixVertexFiniteRootDensity c N (m + m) (sixVertexEvenSymmetricLift m q) x = 1 / N := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_sixVertexFiniteRootDensity_positiveHalfCell hc hN hsol j

/--
[abs_positiveHalfGap_mul_finiteRootDensity_sub_inv_width_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricTailJacobian.lean)
-/
@[path]
private lemma abs_positiveHalfGap_mul_finiteRootDensity_sub_inv_width_le_eq
  {c : Real}
  {N m : Nat}
  {q : Fin m → Real}
  {j : Fin m}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hcount : m + m ≤ N)
  (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
  (hsol : SixVertexSatisfiesBetheEquations c N (m + m) (sixVertexEvenSymmetricLift m q)) :
-- imply
  |sixVertexPositiveHalfRootGap q j * sixVertexFiniteRootDensity c N (m + m) (sixVertexEvenSymmetricLift m q) (q j) - 1 / N| ≤ 2 * (sixVertexFiniteRootDensityLipschitzConstant c : Real) * sixVertexPositiveHalfRootGap q j ^ 2 := by
-- proof
  apply StatMech.FrontierD.abs_positiveHalfGap_mul_finiteRootDensity_sub_inv_width_le hc hN hcount hopen hsol j

/--
[sixVertexPositiveHalfRootGap_upper_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricTailJacobian.lean)
-/
@[path]
private lemma sixVertexPositiveHalfRootGap_upper_tail_eq
  {c : Real}
  {N m : Nat}
  {q : Fin m → Real}
  {j : Fin m}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hN : 0 < N)
  (hhalf : N = 2 * (m + m))
  (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
  (hsol : SixVertexSatisfiesBetheEquations c N (m + m) (sixVertexEvenSymmetricLift m q)) :
-- imply
  sixVertexPositiveHalfRootGap q j ≤ 1 / ((N : Real) * sixVertexTailFiniteDensityFloor c) := by
-- proof
  apply StatMech.FrontierD.sixVertexPositiveHalfRootGap_upper_tail hc htail hN hhalf hopen hsol j

/--
[sixVertexPositiveHalfRootGap_upper_of_finiteDensityLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricTailJacobian.lean)
-/
@[path]
private lemma sixVertexPositiveHalfRootGap_upper_of_finiteDensityLower_eq
  {c : Real}
  {N m : Nat}
  {q : Fin m → Real}
  {lower : Real}
  {j : Fin m}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
  (hsol : SixVertexSatisfiesBetheEquations c N (m + m) (sixVertexEvenSymmetricLift m q))
  (hlower : 0 < lower)
  (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N (m + m) (sixVertexEvenSymmetricLift m q) x) :
-- imply
  sixVertexPositiveHalfRootGap q j ≤ 1 / ((N : Real) * lower) := by
-- proof
  apply StatMech.FrontierD.sixVertexPositiveHalfRootGap_upper_of_finiteDensityLower hc hN hopen hsol hlower hdensity j

/--
[abs_sixVertexBethePositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le_of_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricTailJacobian.lean)
-/
@[path]
private lemma abs_sixVertexBethePositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le_of_lower_eq
  {c : Real}
  {N m : Nat}
  {q : Fin m → Real}
  {lower : Real}
  {j : Fin m}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hcount : m + m ≤ N)
  (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
  (hsol : SixVertexSatisfiesBetheEquations c N (m + m) (sixVertexEvenSymmetricLift m q))
  (hlower : 0 < lower)
  (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N (m + m) (sixVertexEvenSymmetricLift m q) x) :
-- imply
  |sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j j - 2 * Real.pi| ≤ sixVertexSymmetricJacobianDiagonalErrorOfLower c N lower := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexBethePositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le_of_lower hc hN hcount hopen hsol hlower hdensity j

/--
[abs_sixVertexBethePositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricTailJacobian.lean)
-/
@[path]
private lemma abs_sixVertexBethePositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le_tail_eq
  {c : Real}
  {N m : Nat}
  {q : Fin m → Real}
  {j : Fin m}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hN : 0 < N)
  (hhalf : N = 2 * (m + m))
  (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
  (hsol : SixVertexSatisfiesBetheEquations c N (m + m) (sixVertexEvenSymmetricLift m q)) :
-- imply
  |sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j j - 2 * Real.pi| ≤ sixVertexSymmetricTailJacobianDiagonalError c N := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexBethePositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le_tail hc htail hN hhalf hopen hsol j


-- created on 2026-10-23
