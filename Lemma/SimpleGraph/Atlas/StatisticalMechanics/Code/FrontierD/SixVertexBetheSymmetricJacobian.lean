import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricJacobian.Part3
open Finset Matrix StatMech StatMech.FrontierD


/--
[sixVertexEvenSymmetricBetheRootJacobian_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricJacobian.lean)
-/
@[path]
private lemma sixVertexEvenSymmetricBetheRootJacobian_apply_eq
  {N m : Nat}
  {c : Real}
  {q v : Fin m → Real}
  {j : Fin m}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexEvenSymmetricBetheRootJacobian N m c q v j = sixVertexBetheRootJacobian N (m + m) c (sixVertexEvenSymmetricLift m q) (sixVertexEvenSymmetricLift m v) (Fin.natAdd m j) := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenSymmetricBetheRootJacobian_apply hc q v j

/--
[sixVertexEvenSymmetricBetheRootJacobian_toMatrix'_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricJacobian.lean)
-/
@[path]
private lemma sixVertexEvenSymmetricBetheRootJacobian_toMatrix'_apply_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real}
  {j k : Fin m}
-- given
  (hc : 2 < c) :
-- imply
  LinearMap.toMatrix' (sixVertexEvenSymmetricBetheRootJacobian N m c q).toLinearMap j k = sixVertexBethePositiveHalfJacobianMatrix N m c q j k := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenSymmetricBetheRootJacobian_toMatrix'_apply hc q j k

/--
[sixVertexEvenSymmetricBetheRootJacobian_injective_of_diagonalDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricJacobian.lean)
-/
@[path]
private lemma sixVertexEvenSymmetricBetheRootJacobian_injective_of_diagonalDominance_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real}
-- given
  (hc : 2 < c)
  (hdom : ∀ j, ∑ k ∈ Finset.univ.erase j, ‖sixVertexBethePositiveHalfJacobianMatrix N m c q j k‖ < ‖sixVertexBethePositiveHalfJacobianMatrix N m c q j j‖) :
-- imply
  Function.Injective (sixVertexEvenSymmetricBetheRootJacobian N m c q) := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenSymmetricBetheRootJacobian_injective_of_diagonalDominance hc q hdom

/--
[sixVertexEvenSymmetricLift_positive_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricJacobian.lean)
-/
@[path]
private lemma sixVertexEvenSymmetricLift_positive_mem_Icc_eq
  {m : Nat}
  {q : Fin m → Real}
  {j : Fin m}
-- given
  (hq : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q)) :
-- imply
  q j ∈ Set.Icc 0 Real.pi := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenSymmetricLift_positive_mem_Icc hq j

/--
[sixVertexBethePositiveHalfJacobianMatrix_offdiag_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricJacobian.lean)
-/
@[path]
private lemma sixVertexBethePositiveHalfJacobianMatrix_offdiag_nonneg_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real}
  {j k : Fin m}
-- given
  (hc : 2 < c)
  (hq : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
  (hjk : j ≠ k) :
-- imply
  0 ≤ sixVertexBethePositiveHalfJacobianMatrix N m c q j k := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePositiveHalfJacobianMatrix_offdiag_nonneg hc hq hjk

/--
[sixVertexBethePositiveHalfJacobianMatrix_mul_gap_offdiag_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricJacobian.lean)
-/
@[path]
private lemma sixVertexBethePositiveHalfJacobianMatrix_mul_gap_offdiag_nonneg_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real}
  {gap : Fin m → Real}
  {j k : Fin m}
-- given
  (hc : 2 < c)
  (hq : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
  (hgap : ∀ k, 0 ≤ gap k)
  (hjk : j ≠ k) :
-- imply
  0 ≤ sixVertexBethePositiveHalfJacobianMatrix N m c q j k * gap k := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePositiveHalfJacobianMatrix_mul_gap_offdiag_nonneg hc hq gap hgap hjk

/--
[sixVertexPositiveHalfRootGap_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricJacobian.lean)
-/
@[path]
private lemma sixVertexPositiveHalfRootGap_pos_eq
  {m : Nat}
  {q : Fin m → Real}
  {k : Fin m}
-- given
  (hqmono : StrictMono q)
  (hqpos : ∀ k, 0 < q k) :
-- imply
  0 < sixVertexPositiveHalfRootGap q k := by
-- proof
  apply StatMech.FrontierD.sixVertexPositiveHalfRootGap_pos hqmono hqpos k

/--
[sixVertexEvenSymmetricLift_positive_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricJacobian.lean)
-/
@[path]
private lemma sixVertexEvenSymmetricLift_positive_strictMono_eq
  {m : Nat}
  {q : Fin m → Real}
-- given
  (hq : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q)) :
-- imply
  StrictMono q := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenSymmetricLift_positive_strictMono hq

/--
[sixVertexPositiveHalfRootGap_pos_of_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricJacobian.lean)
-/
@[path]
private lemma sixVertexPositiveHalfRootGap_pos_of_open_eq
  {m : Nat}
  {q : Fin m → Real}
  {k : Fin m}
-- given
  (hq : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q)) :
-- imply
  0 < sixVertexPositiveHalfRootGap q k := by
-- proof
  apply StatMech.FrontierD.sixVertexPositiveHalfRootGap_pos_of_open hq k

/--
[sixVertexBethePositiveHalfScaledJacobianMatrix_eq_mul_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricJacobian.lean)
-/
@[path]
private lemma sixVertexBethePositiveHalfScaledJacobianMatrix_eq_mul_diagonal_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real} :
-- imply
  sixVertexBethePositiveHalfScaledJacobianMatrix N m c q = sixVertexBethePositiveHalfJacobianMatrix N m c q * Matrix.diagonal (sixVertexPositiveHalfRootGap q) := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePositiveHalfScaledJacobianMatrix_eq_mul_diagonal N m c q

/--
[sixVertexBethePositiveHalfScaledJacobianMatrix_offdiag_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricJacobian.lean)
-/
@[path]
private lemma sixVertexBethePositiveHalfScaledJacobianMatrix_offdiag_nonneg_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real}
  {j k : Fin m}
-- given
  (hc : 2 < c)
  (hq : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
  (hjk : j ≠ k) :
-- imply
  0 ≤ sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j k := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePositiveHalfScaledJacobianMatrix_offdiag_nonneg hc hq hjk

/--
[sixVertexBethePositiveHalfJacobianMatrix_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricJacobian.lean)
-/
@[path]
private lemma sixVertexBethePositiveHalfJacobianMatrix_diag_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real}
  {j : Fin m} :
-- imply
  sixVertexBethePositiveHalfJacobianMatrix N m c q j j = (N : Real) + ∑ l ∈ Finset.univ.erase (Fin.natAdd m j), 4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (sixVertexEvenSymmetricLift m q l) / sixVertexThetaDerivativeDenominator c (sixVertexEvenSymmetricLift m q (Fin.natAdd m j)) (sixVertexEvenSymmetricLift m q l) - (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (sixVertexEvenSymmetricLift m q (Fin.natAdd m j)) / sixVertexThetaDerivativeDenominator c (sixVertexEvenSymmetricLift m q (Fin.natAdd m j)) (sixVertexEvenSymmetricLift m q (Fin.castAdd m j.rev))) := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePositiveHalfJacobianMatrix_diag N m c q j

/--
[sixVertexBethePositiveHalfScaledJacobianMatrix_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricJacobian.lean)
-/
@[path]
private lemma sixVertexBethePositiveHalfScaledJacobianMatrix_diag_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real}
  {j : Fin m} :
-- imply
  sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j j = ((N : Real) + ∑ l ∈ Finset.univ.erase (Fin.natAdd m j), 4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (sixVertexEvenSymmetricLift m q l) / sixVertexThetaDerivativeDenominator c (sixVertexEvenSymmetricLift m q (Fin.natAdd m j)) (sixVertexEvenSymmetricLift m q l) - (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (sixVertexEvenSymmetricLift m q (Fin.natAdd m j)) / sixVertexThetaDerivativeDenominator c (sixVertexEvenSymmetricLift m q (Fin.natAdd m j)) (sixVertexEvenSymmetricLift m q (Fin.castAdd m j.rev)))) * sixVertexPositiveHalfRootGap q j := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePositiveHalfScaledJacobianMatrix_diag N m c q j

/--
[sixVertexEvenSymmetricBetheRootJacobian_injective_of_scaledDiagonalDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricJacobian.lean)
-/
@[path]
private lemma sixVertexEvenSymmetricBetheRootJacobian_injective_of_scaledDiagonalDominance_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real}
-- given
  (hc : 2 < c)
  (hgap : ∀ k, sixVertexPositiveHalfRootGap q k ≠ 0)
  (hdom : ∀ j, ∑ k ∈ Finset.univ.erase j, ‖sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j k‖ < ‖sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j j‖) :
-- imply
  Function.Injective (sixVertexEvenSymmetricBetheRootJacobian N m c q) := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenSymmetricBetheRootJacobian_injective_of_scaledDiagonalDominance hc q hgap hdom


-- created on 2026-10-23
