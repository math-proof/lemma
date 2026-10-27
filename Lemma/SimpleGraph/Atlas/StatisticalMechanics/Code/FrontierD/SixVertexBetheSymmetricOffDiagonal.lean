import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricOffDiagonal.Part3
open Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexNegativeHalfRootPartition_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricOffDiagonal.lean)
-/
@[path]
private lemma sixVertexNegativeHalfRootPartition_of_lt_eq
  {m : Nat}
  {q : Fin m → Real}
  {k : Nat}
-- given
  (hm : 0 < m)
  (hk : k < m) :
-- imply
  sixVertexNegativeHalfRootPartition q hm k = -q ⟨m - 1 - k, by omega⟩ := by
-- proof
  apply StatMech.FrontierD.sixVertexNegativeHalfRootPartition_of_lt q hm hk

/--
[sixVertexNegativeHalfRootPartition_end](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricOffDiagonal.lean)
-/
@[path]
private lemma sixVertexNegativeHalfRootPartition_end_eq
  {m : Nat}
  {q : Fin m → Real}
-- given
  (hm : 0 < m) :
-- imply
  sixVertexNegativeHalfRootPartition q hm m = q ⟨0, hm⟩ := by
-- proof
  apply StatMech.FrontierD.sixVertexNegativeHalfRootPartition_end q hm

/--
[sixVertexNegativeHalfRootPartition_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricOffDiagonal.lean)
-/
@[path]
private lemma sixVertexNegativeHalfRootPartition_zero_eq
  {m : Nat}
  {q : Fin m → Real}
-- given
  (hm : 0 < m) :
-- imply
  sixVertexNegativeHalfRootPartition q hm 0 = -q ⟨m - 1, by omega⟩ := by
-- proof
  apply StatMech.FrontierD.sixVertexNegativeHalfRootPartition_zero q hm

/--
[sixVertexNegativeHalfRootPartition_cellGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricOffDiagonal.lean)
-/
@[path]
private lemma sixVertexNegativeHalfRootPartition_cellGap_eq
  {m : Nat}
  {q : Fin m → Real}
  {k : Nat}
-- given
  (hm : 0 < m)
  (hk : k < m) :
-- imply
  sixVertexNegativeHalfRootPartition q hm (k + 1) - sixVertexNegativeHalfRootPartition q hm k = sixVertexPositiveHalfRootGap q ⟨m - 1 - k, by omega⟩ := by
-- proof
  apply StatMech.FrontierD.sixVertexNegativeHalfRootPartition_cellGap q hm k hk

/--
[sixVertexNegativeHalfRootPartition_ordered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricOffDiagonal.lean)
-/
@[path]
private lemma sixVertexNegativeHalfRootPartition_ordered_eq
  {m : Nat}
  {q : Fin m → Real}
-- given
  (hm : 0 < m)
  (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q)) :
-- imply
  ∀ k < m, sixVertexNegativeHalfRootPartition q hm k ≤ sixVertexNegativeHalfRootPartition q hm (k + 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexNegativeHalfRootPartition_ordered hm hopen

/--
[sixVertexNegativeHalfRootPartition_fin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricOffDiagonal.lean)
-/
@[path]
private lemma sixVertexNegativeHalfRootPartition_fin_eq
  {m : Nat}
  {q : Fin m → Real}
  {k : Fin m}
-- given
  (hm : 0 < m) :
-- imply
  sixVertexNegativeHalfRootPartition q hm k.val = -q k.rev := by
-- proof
  apply StatMech.FrontierD.sixVertexNegativeHalfRootPartition_fin q hm k

/--
[sixVertexNegativeHalfRootPartition_fin_cellGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricOffDiagonal.lean)
-/
@[path]
private lemma sixVertexNegativeHalfRootPartition_fin_cellGap_eq
  {m : Nat}
  {q : Fin m → Real}
  {k : Fin m}
-- given
  (hm : 0 < m) :
-- imply
  sixVertexNegativeHalfRootPartition q hm (k.val + 1) - sixVertexNegativeHalfRootPartition q hm k.val = sixVertexPositiveHalfRootGap q k.rev := by
-- proof
  apply StatMech.FrontierD.sixVertexNegativeHalfRootPartition_fin_cellGap q hm k

/--
[abs_positiveHalfScatteringEndpointSum_sub_integral_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricOffDiagonal.lean)
-/
@[path]
private lemma abs_positiveHalfScatteringEndpointSum_sub_integral_le_eq
  {c : Real}
  {m : Nat}
  {q : Fin m → Real}
  {mesh : Real}
  {j : Fin m}
-- given
  (hc : 2 < c)
  (hm : 0 < m)
  (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
  (hmesh : ∀ k, sixVertexPositiveHalfRootGap q k ≤ mesh) :
-- imply
  |∑ k, sixVertexPositiveHalfRootGap q k * sixVertexSymmetricScatteringDerivative c (-q j) (-q k) - ∫ y in -q ⟨m - 1, by omega⟩..q ⟨0, hm⟩, sixVertexSymmetricScatteringDerivative c (-q j) y| ≤ (sixVertexSymmetricScatteringLipschitzConstant c : Real) * mesh * (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierD.abs_positiveHalfScatteringEndpointSum_sub_integral_le hc hm hopen hmesh j

/--
[sixVertexBethePositiveHalfJacobianMatrix_offdiag_eq_scatteringDerivative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricOffDiagonal.lean)
-/
@[path]
private lemma sixVertexBethePositiveHalfJacobianMatrix_offdiag_eq_scatteringDerivative_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real}
  {j k : Fin m}
-- given
  (hjk : j ≠ k) :
-- imply
  sixVertexBethePositiveHalfJacobianMatrix N m c q j k = sixVertexSymmetricScatteringDerivative c (-q j) (-q k) := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePositiveHalfJacobianMatrix_offdiag_eq_scatteringDerivative hjk

/--
[sixVertexSymmetricScatteringDerivative_odd_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricOffDiagonal.lean)
-/
@[path]
private lemma sixVertexSymmetricScatteringDerivative_odd_right_eq
  {c x y : Real} :
-- imply
  sixVertexSymmetricScatteringDerivative c x (-y) = -sixVertexSymmetricScatteringDerivative c x y := by
-- proof
  apply StatMech.FrontierD.sixVertexSymmetricScatteringDerivative_odd_right c x y

/--
[sixVertexSymmetricScatteringPhase_even_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricOffDiagonal.lean)
-/
@[path]
private lemma sixVertexSymmetricScatteringPhase_even_right_eq
  {c x y : Real} :
-- imply
  sixVertexSymmetricScatteringPhase c x (-y) = sixVertexSymmetricScatteringPhase c x y := by
-- proof
  apply StatMech.FrontierD.sixVertexSymmetricScatteringPhase_even_right c x y

/--
[intervalIntegral_sixVertexSymmetricScatteringDerivative_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricOffDiagonal.lean)
-/
@[path]
private lemma intervalIntegral_sixVertexSymmetricScatteringDerivative_symmetric_eq
  {c : Real}
  {x a : Real}
-- given
  (hc : 2 < c) :
-- imply
  ∫ y in -a..a, sixVertexSymmetricScatteringDerivative c x y = 0 := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_sixVertexSymmetricScatteringDerivative_symmetric hc x a

/--
[intervalIntegral_sixVertexSymmetricScatteringDerivative_root_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricOffDiagonal.lean)
-/
@[path]
private lemma intervalIntegral_sixVertexSymmetricScatteringDerivative_root_bounds_eq
  {c : Real}
  {m : Nat}
  {q : Fin m → Real}
  {j k0 kmax : Fin m}
-- given
  (hc : 2 < c)
  (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
  (hk0 : q k0 ≤ q kmax) :
-- imply
  0 ≤ ∫ y in -q kmax..q k0, sixVertexSymmetricScatteringDerivative c (-q j) y ∧ (∫ y in -q kmax..q k0, sixVertexSymmetricScatteringDerivative c (-q j) y) ≤ sixVertexSymmetricScatteringBoundaryBound c := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_sixVertexSymmetricScatteringDerivative_root_bounds hc hopen j k0 kmax hk0

/--
[abs_sixVertexBethePositiveHalfScaledJacobianMatrix_offdiagSum_sub_integral_le_of_mesh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricOffDiagonal.lean)
-/
@[path]
private lemma abs_sixVertexBethePositiveHalfScaledJacobianMatrix_offdiagSum_sub_integral_le_of_mesh_eq
  {c : Real}
  {N m : Nat}
  {q : Fin m → Real}
  {mesh : Real}
  {j : Fin m}
-- given
  (hc : 2 < c)
  (hm : 0 < m)
  (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
  (hmesh : ∀ k, sixVertexPositiveHalfRootGap q k ≤ mesh) :
-- imply
  |(∑ k ∈ Finset.univ.erase j, sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j k) - ∫ y in -q ⟨m - 1, by omega⟩..q ⟨0, hm⟩, sixVertexSymmetricScatteringDerivative c (-q j) y| ≤ ((2 * Real.pi) * (sixVertexSymmetricScatteringLipschitzConstant c : Real) + 2 * (sixVertexAnisotropyMagnitude c / (sixVertexAnisotropyMagnitude c - 1))) * mesh := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexBethePositiveHalfScaledJacobianMatrix_offdiagSum_sub_integral_le_of_mesh hc hm hopen hmesh j

/--
[abs_sixVertexBethePositiveHalfScaledJacobianMatrix_offdiagSum_sub_integral_le_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricOffDiagonal.lean)
-/
@[path]
private lemma abs_sixVertexBethePositiveHalfScaledJacobianMatrix_offdiagSum_sub_integral_le_tail_eq
  {c : Real}
  {N m : Nat}
  {q : Fin m → Real}
  {j : Fin m}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hm : 0 < m)
  (hN : 0 < N)
  (hhalf : N = 2 * (m + m))
  (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
  (hsol : SixVertexSatisfiesBetheEquations c N (m + m) (sixVertexEvenSymmetricLift m q)) :
-- imply
  |(∑ k ∈ Finset.univ.erase j, sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j k) - ∫ y in -q ⟨m - 1, by omega⟩..q ⟨0, hm⟩, sixVertexSymmetricScatteringDerivative c (-q j) y| ≤ sixVertexSymmetricTailJacobianOffDiagonalError c N := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexBethePositiveHalfScaledJacobianMatrix_offdiagSum_sub_integral_le_tail hc htail hm hN hhalf hopen hsol j

/--
[sixVertexEvenSymmetricBetheRootJacobian_injective_of_finiteDensityLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricOffDiagonal.lean)
-/
@[path]
private lemma sixVertexEvenSymmetricBetheRootJacobian_injective_of_finiteDensityLower_eq
  {c : Real}
  {N m : Nat}
  {q : Fin m → Real}
  {lower : Real}
-- given
  (hc : 2 < c)
  (hm : 0 < m)
  (hN : 0 < N)
  (hcount : m + m ≤ N)
  (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
  (hsol : SixVertexSatisfiesBetheEquations c N (m + m) (sixVertexEvenSymmetricLift m q))
  (hlower : 0 < lower)
  (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N (m + m) (sixVertexEvenSymmetricLift m q) x)
  (hmargin : sixVertexSymmetricScatteringBoundaryBound c + 2 * sixVertexSymmetricJacobianTotalErrorOfLower c N lower < 2 * Real.pi) :
-- imply
  Function.Injective (sixVertexEvenSymmetricBetheRootJacobian N m c q) := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenSymmetricBetheRootJacobian_injective_of_finiteDensityLower hc hm hN hcount hopen hsol hlower hdensity hmargin

/--
[sixVertexEvenSymmetricBetheRootJacobian_injective_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricOffDiagonal.lean)
-/
@[path]
private lemma sixVertexEvenSymmetricBetheRootJacobian_injective_tail_eq
  {c : Real}
  {N m : Nat}
  {q : Fin m → Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hm : 0 < m)
  (hN : 0 < N)
  (hhalf : N = 2 * (m + m))
  (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
  (hsol : SixVertexSatisfiesBetheEquations c N (m + m) (sixVertexEvenSymmetricLift m q))
  (hmargin : sixVertexSymmetricScatteringBoundaryBound c + 2 * sixVertexSymmetricTailJacobianTotalError c N < 2 * Real.pi) :
-- imply
  Function.Injective (sixVertexEvenSymmetricBetheRootJacobian N m c q) := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenSymmetricBetheRootJacobian_injective_tail hc htail hm hN hhalf hopen hsol hmargin

/--
[sixVertexSymmetricTailJacobianTotalError_fourWidth_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricOffDiagonal.lean)
-/
@[path]
private lemma sixVertexSymmetricTailJacobianTotalError_fourWidth_tendsto_zero_eq
  {c : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  Tendsto (fun k : Nat => sixVertexSymmetricTailJacobianTotalError c (sixVertexFourWidth 0 k)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.sixVertexSymmetricTailJacobianTotalError_fourWidth_tendsto_zero hc htail

/--
[eventually_sixVertexSymmetricTailJacobian_margin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricOffDiagonal.lean)
-/
@[path]
private lemma eventually_sixVertexSymmetricTailJacobian_margin_eq
  {c : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  ∀ᶠ k : Nat in atTop, sixVertexSymmetricScatteringBoundaryBound c + 2 * sixVertexSymmetricTailJacobianTotalError c (sixVertexFourWidth 0 k) < 2 * Real.pi := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexSymmetricTailJacobian_margin hc htail

/--
[eventually_sixVertexSelectedEvenSymmetricBetheRootJacobian_injective_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricOffDiagonal.lean)
-/
@[path]
private lemma eventually_sixVertexSelectedEvenSymmetricBetheRootJacobian_injective_tail_eq
  {c : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  ∀ᶠ k : Nat in atTop, Function.Injective (sixVertexEvenSymmetricBetheRootJacobian (sixVertexFourWidth 0 k) (k + 1) c (sixVertexPositiveHalfBetheRoots hc k)) := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexSelectedEvenSymmetricBetheRootJacobian_injective_tail hc htail


-- created on 2026-10-23
