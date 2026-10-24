import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheJacobianStability
open Finset Filter Topology Matrix StatMech StatMech.FrontierD


/--
[sixVertexBetheRootJacobian_toMatrix'_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheJacobianStability.lean)
-/
@[path]
private lemma sixVertexBetheRootJacobian_toMatrix'_apply_eq
  {N n : Nat}
  {c : Real}
  {p : Fin n → Real}
  {j k : Fin n}
-- given
  (hc : 2 < c) :
-- imply
  LinearMap.toMatrix' (sixVertexBetheRootJacobian N n c p).toLinearMap j k = sixVertexBetheJacobianMatrix N n c p j k := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheRootJacobian_toMatrix'_apply hc p j k

/--
[one_lt_sixVertexAnisotropyMagnitude](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheJacobianStability.lean)
-/
@[path]
private lemma one_lt_sixVertexAnisotropyMagnitude_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  1 < sixVertexAnisotropyMagnitude c := by
-- proof
  apply StatMech.FrontierD.one_lt_sixVertexAnisotropyMagnitude hc

/--
[sixVertexThetaDerivativeDenominator_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheJacobianStability.lean)
-/
@[path]
private lemma sixVertexThetaDerivativeDenominator_eq_eq
  {c x y : Real} :
-- imply
  sixVertexThetaDerivativeDenominator c x y = 4 * sixVertexBetheIntegratingFactor c x * sixVertexBetheIntegratingFactor c y + 2 * (1 - Real.cos (x - y)) := by
-- proof
  apply StatMech.FrontierD.sixVertexThetaDerivativeDenominator_eq c x y

/--
[norm_sixVertexTheta_rightDerivative_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheJacobianStability.lean)
-/
@[path]
private lemma norm_sixVertexTheta_rightDerivative_le_eq
  {c : Real}
  {x y : Real}
-- given
  (hc : 2 < c) :
-- imply
  ‖-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x / sixVertexThetaDerivativeDenominator c x y‖ ≤ sixVertexAnisotropyMagnitude c / (sixVertexAnisotropyMagnitude c - 1) := by
-- proof
  apply StatMech.FrontierD.norm_sixVertexTheta_rightDerivative_le hc x y

/--
[norm_sixVertexTheta_leftDerivative_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheJacobianStability.lean)
-/
@[path]
private lemma norm_sixVertexTheta_leftDerivative_le_eq
  {c : Real}
  {x y : Real}
-- given
  (hc : 2 < c) :
-- imply
  ‖4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y / sixVertexThetaDerivativeDenominator c x y‖ ≤ sixVertexAnisotropyMagnitude c / (sixVertexAnisotropyMagnitude c - 1) := by
-- proof
  apply StatMech.FrontierD.norm_sixVertexTheta_leftDerivative_le hc x y

/--
[sixVertexBetheRootJacobian_injective_of_diagonalDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheJacobianStability.lean)
-/
@[path]
private lemma sixVertexBetheRootJacobian_injective_of_diagonalDominance_eq
  {N n : Nat}
  {c : Real}
  {p : Fin n → Real}
-- given
  (hc : 2 < c)
  (hdom : 2 * ((n : Real) - 1) * (sixVertexAnisotropyMagnitude c / (sixVertexAnisotropyMagnitude c - 1)) < (N : Real)) :
-- imply
  Function.Injective (sixVertexBetheRootJacobian N n c p) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheRootJacobian_injective_of_diagonalDominance hc p hdom

/--
[sixVertexBetheRootJacobian_injective_of_anisotropyMagnitude](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheJacobianStability.lean)
-/
@[path]
private lemma sixVertexBetheRootJacobian_injective_of_anisotropyMagnitude_eq
  {N n : Nat}
  {c : Real}
  {p : Fin n → Real}
-- given
  (hc : 2 < c)
  (hhalf : 2 * n ≤ N)
  (htail : (n : Real) < sixVertexAnisotropyMagnitude c) :
-- imply
  Function.Injective (sixVertexBetheRootJacobian N n c p) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheRootJacobian_injective_of_anisotropyMagnitude hc hhalf htail p

/--
[sixVertexAnisotropyMagnitude_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheJacobianStability.lean)
-/
@[path]
private lemma sixVertexAnisotropyMagnitude_mono_eq
  {a c : Real}
-- given
  (ha : 0 ≤ a)
  (hac : a ≤ c) :
-- imply
  sixVertexAnisotropyMagnitude a ≤ sixVertexAnisotropyMagnitude c := by
-- proof
  apply StatMech.FrontierD.sixVertexAnisotropyMagnitude_mono ha hac

/--
[exists_sixVertexContinuousBetheBranch_of_anisotropyMagnitude](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheJacobianStability.lean)
-/
@[path]
private lemma exists_sixVertexContinuousBetheBranch_of_anisotropyMagnitude_eq
  {a b c₀ : Real}
  {N n : Nat}
  {z₀ : SixVertexBetheContinuationSpace a b N n}
-- given
  (ha : 2 < a)
  (hab : a ≤ b)
  (hc₀ : c₀ ∈ Set.Icc a b)
  (hN : 0 < N)
  (hhalf : 2 * n ≤ N)
  (htail : (n : Real) < sixVertexAnisotropyMagnitude a)
  (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩) :
-- imply
  ∃ roots : C(Real, Fin n → Real), roots c₀ = z₀.1.2 ∧ ∀ t ∈ Set.Icc a b, SixVertexSatisfiesBetheEquations t N n (roots t) := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexContinuousBetheBranch_of_anisotropyMagnitude ha hab hc₀ hN hhalf htail z₀ hz₀

/--
[exists_sixVertexAnalyticBetheBranch_of_anisotropyMagnitude](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheJacobianStability.lean)
-/
@[path]
private lemma exists_sixVertexAnalyticBetheBranch_of_anisotropyMagnitude_eq
  {a b c₀ : Real}
  {N n : Nat}
  {z₀ : SixVertexBetheContinuationSpace a b N n}
-- given
  (ha : 2 < a)
  (hab : a ≤ b)
  (hc₀ : c₀ ∈ Set.Icc a b)
  (hN : 0 < N)
  (hhalf : 2 * n ≤ N)
  (htail : (n : Real) < sixVertexAnisotropyMagnitude a)
  (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩) :
-- imply
  ∃ roots : C(Real, Fin n → Real), roots c₀ = z₀.1.2 ∧ (∀ t ∈ Set.Icc a b, SixVertexSatisfiesBetheEquations t N n (roots t)) ∧ ∀ t ∈ Set.Ioo a b, AnalyticAt Real roots t := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexAnalyticBetheBranch_of_anisotropyMagnitude ha hab hc₀ hN hhalf htail z₀ hz₀

/--
[exists_sixVertexAnalyticBetheBranch_throughChosen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheJacobianStability.lean)
-/
@[path]
private lemma exists_sixVertexAnalyticBetheBranch_throughChosen_eq
  {a b c₀ : Real}
  {N n : Nat}
-- given
  (ha : 2 < a)
  (hab : a ≤ b)
  (hc₀ : c₀ ∈ Set.Icc a b)
  (hN : 0 < N)
  (hhalf : 2 * n ≤ N)
  (htail : (n : Real) < sixVertexAnisotropyMagnitude a) :
-- imply
  ∃ roots : C(Real, Fin n → Real), roots c₀ = sixVertexChosenBetheSolution (ha.trans_le hc₀.1) hhalf ∧ (∀ t ∈ Set.Icc a b, SixVertexSatisfiesBetheEquations t N n (roots t)) ∧ ∀ t ∈ Set.Ioo a b, AnalyticAt Real roots t := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexAnalyticBetheBranch_throughChosen ha hab hc₀ hN hhalf htail

/--
[sixVertexFirstHalfIndex_lt_reflected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheJacobianStability.lean)
-/
@[path]
private lemma sixVertexFirstHalfIndex_lt_reflected_eq
  {m : Nat}
  {j : Fin m} :
-- imply
  sixVertexFirstHalfIndex m j < sixVertexReflectedHalfIndex m j := by
-- proof
  apply StatMech.FrontierD.sixVertexFirstHalfIndex_lt_reflected m j

/--
[sixVertexFirstHalfRoot_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheJacobianStability.lean)
-/
@[path]
private lemma sixVertexFirstHalfRoot_mem_Icc_eq
  {m : Nat}
  {p : Fin (m + m) → Real}
  {j : Fin m}
-- given
  (hp : SixVertexOpenRootSimplex p) :
-- imply
  p (sixVertexFirstHalfIndex m j) ∈ Set.Icc (-Real.pi) 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexFirstHalfRoot_mem_Icc hp j

/--
[sixVertexThetaDerivativeDenominator_neg_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheJacobianStability.lean)
-/
@[path]
private lemma sixVertexThetaDerivativeDenominator_neg_right_eq
  {c x y : Real} :
-- imply
  sixVertexThetaDerivativeDenominator c x (-y) = sixVertexThetaDerivativeDenominator c (-x) y := by
-- proof
  apply StatMech.FrontierD.sixVertexThetaDerivativeDenominator_neg_right c x y

/--
[sixVertexBetheSymmetricHalfJacobianMatrix_offdiag_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheJacobianStability.lean)
-/
@[path]
private lemma sixVertexBetheSymmetricHalfJacobianMatrix_offdiag_nonneg_eq
  {N m : Nat}
  {c : Real}
  {p : Fin (m + m) → Real}
  {j k : Fin m}
-- given
  (hc : 2 < c)
  (hp : SixVertexOpenRootSimplex p)
  (hjk : j ≠ k) :
-- imply
  0 ≤ sixVertexBetheSymmetricHalfJacobianMatrix N m c p j k := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheSymmetricHalfJacobianMatrix_offdiag_nonneg hc hp hjk


-- created on 2026-10-23
