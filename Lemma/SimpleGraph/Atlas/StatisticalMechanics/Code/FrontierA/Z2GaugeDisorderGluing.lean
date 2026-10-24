import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.Z2GaugeDisorderGluing
open Finset StatMech StatMech.FrontierA


/--
[multibondIsingAction_coupling_sub_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean)
-/
@[path]
private lemma multibondIsingAction_coupling_sub_abs_le_eq
  [Fintype P]
  [DecidableEq P]
  {ends : P → V × V}
  {J J' : P → Real}
  {s : V → Bool} :
-- imply
  |multibondIsingAction ends J s - multibondIsingAction ends J' s| ≤ ∑ p : P, |J p - J' p| := by
-- proof
  apply StatMech.FrontierA.multibondIsingAction_coupling_sub_abs_le ends J J' s

/--
[multibondIsing_logPartition_coupling_sub_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean)
-/
@[path]
private lemma multibondIsing_logPartition_coupling_sub_abs_le_eq
  [Fintype P]
  [DecidableEq P]
  {ends : P → V × V}
  {J J' : P → Real} :
-- imply
  |Real.log (multibondIsingPartition ends J) - Real.log (multibondIsingPartition ends J')| ≤ ∑ p : P, |J p - J' p| := by
-- proof
  apply StatMech.FrontierA.multibondIsing_logPartition_coupling_sub_abs_le ends J J'

/--
[abs_multibondTwistCoupling_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean)
-/
@[path]
private lemma abs_multibondTwistCoupling_sub_eq
  [Fintype P]
  [DecidableEq P]
  {J J' : P → Real}
  {D : Finset P}
  {p : P} :
-- imply
  |multibondTwistCoupling J D p - multibondTwistCoupling J' D p| = |J p - J' p| := by
-- proof
  apply StatMech.FrontierA.abs_multibondTwistCoupling_sub J J' D p

/--
[multibondDisorderFreeEnergy_coupling_sub_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean)
-/
@[path]
private lemma multibondDisorderFreeEnergy_coupling_sub_abs_le_eq
  [Fintype P]
  [DecidableEq P]
  {ends : P → V × V}
  {J J' : P → Real}
  {D : Finset P} :
-- imply
  |multibondDisorderFreeEnergy ends J D - multibondDisorderFreeEnergy ends J' D| ≤ 2 * ∑ p : P, |J p - J' p| := by
-- proof
  apply StatMech.FrontierA.multibondDisorderFreeEnergy_coupling_sub_abs_le ends J J' D

/--
[sum_abs_sub_eraseMultibondCouplings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean)
-/
@[path]
private lemma sum_abs_sub_eraseMultibondCouplings_eq
  [Fintype P]
  [DecidableEq P]
  {J : P → Real}
  {S : Finset P} :
-- imply
  (∑ p : P, |J p - eraseMultibondCouplings J S p|) = ∑ p ∈ S, |J p| := by
-- proof
  apply StatMech.FrontierA.sum_abs_sub_eraseMultibondCouplings J S

/--
[multibondDisorderFreeEnergy_eraseSeam_sub_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean)
-/
@[path]
private lemma multibondDisorderFreeEnergy_eraseSeam_sub_abs_le_eq
  [Fintype P]
  [DecidableEq P]
  {ends : P → V × V}
  {J : P → Real}
  {D S : Finset P} :
-- imply
  |multibondDisorderFreeEnergy ends J D - multibondDisorderFreeEnergy ends (eraseMultibondCouplings J S) D| ≤ 2 * ∑ p ∈ S, |J p| := by
-- proof
  apply StatMech.FrontierA.multibondDisorderFreeEnergy_eraseSeam_sub_abs_le ends J D S

/--
[multibondDisorderFreeEnergy_le_blockCost_add_seam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean)
-/
@[path]
private lemma multibondDisorderFreeEnergy_le_blockCost_add_seam_eq
  [Fintype P]
  [DecidableEq P]
  {ends : P → V × V}
  {J : P → Real}
  {D S : Finset P}
  {blockCost : Real}
-- given
  (hblock : multibondDisorderFreeEnergy ends (eraseMultibondCouplings J S) D ≤ blockCost) :
-- imply
  multibondDisorderFreeEnergy ends J D ≤ blockCost + 2 * ∑ p ∈ S, |J p| := by
-- proof
  apply StatMech.FrontierA.multibondDisorderFreeEnergy_le_blockCost_add_seam ends J D S blockCost hblock

/--
[multibondDisorderFreeEnergy_eraseSeam_homogeneous_sub_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean)
-/
@[path]
private lemma multibondDisorderFreeEnergy_eraseSeam_homogeneous_sub_abs_le_eq
  [Fintype P]
  [DecidableEq P]
  {ends : P → V × V}
  {J : Real}
  {D S : Finset P} :
-- imply
  |multibondDisorderFreeEnergy ends (fun _ => J) D - multibondDisorderFreeEnergy ends (eraseMultibondCouplings (fun _ => J) S) D| ≤ 2 * S.card * |J| := by
-- proof
  apply StatMech.FrontierA.multibondDisorderFreeEnergy_eraseSeam_homogeneous_sub_abs_le ends J D S

/--
[cubicalDisorderFreeEnergy_eraseSeam_sub_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean)
-/
@[path]
private lemma cubicalDisorderFreeEnergy_eraseSeam_sub_abs_le_eq
  [Fintype P]
  [DecidableEq P]
  {a b c : Nat}
  {beta : Real}
  {D S : Finset (CubicalPlaquette a b c)}
-- given
  (hbeta : 0 < beta) :
-- imply
  |multibondDisorderFreeEnergy cubicalDualEnds (fun _ => gaugeDualCoupling beta) D - multibondDisorderFreeEnergy cubicalDualEnds (eraseMultibondCouplings (fun _ => gaugeDualCoupling beta) S) D| ≤ 2 * S.card * gaugeDualCoupling beta := by
-- proof
  apply StatMech.FrontierA.cubicalDisorderFreeEnergy_eraseSeam_sub_abs_le hbeta D S

/--
[multibondIsingAction_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean)
-/
@[path]
private lemma multibondIsingAction_sum_eq
  [Fintype P]
  [DecidableEq P]
  {ends₁ : P₁ → V₁ × V₁}
  {ends₂ : P₂ → V₂ × V₂}
  {J₁ : P₁ → Real}
  {J₂ : P₂ → Real}
  {s₁ : V₁ → Bool}
  {s₂ : V₂ → Bool} :
-- imply
  multibondIsingAction (multibondSumEnds ends₁ ends₂) (multibondSumCoupling J₁ J₂) ((Equiv.sumArrowEquivProdArrow V₁ V₂ Bool).symm (s₁, s₂)) = multibondIsingAction ends₁ J₁ s₁ + multibondIsingAction ends₂ J₂ s₂ := by
-- proof
  apply StatMech.FrontierA.multibondIsingAction_sum ends₁ ends₂ J₁ J₂ s₁ s₂

/--
[multibondIsingWeight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean)
-/
@[path]
private lemma multibondIsingWeight_sum_eq
  [Fintype P]
  [DecidableEq P]
  {ends₁ : P₁ → V₁ × V₁}
  {ends₂ : P₂ → V₂ × V₂}
  {J₁ : P₁ → Real}
  {J₂ : P₂ → Real}
  {s₁ : V₁ → Bool}
  {s₂ : V₂ → Bool} :
-- imply
  multibondIsingWeight (multibondSumEnds ends₁ ends₂) (multibondSumCoupling J₁ J₂) ((Equiv.sumArrowEquivProdArrow V₁ V₂ Bool).symm (s₁, s₂)) = multibondIsingWeight ends₁ J₁ s₁ * multibondIsingWeight ends₂ J₂ s₂ := by
-- proof
  apply StatMech.FrontierA.multibondIsingWeight_sum ends₁ ends₂ J₁ J₂ s₁ s₂

/--
[multibondIsingPartition_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean)
-/
@[path]
private lemma multibondIsingPartition_sum_eq
  [Fintype P]
  [DecidableEq P]
  {ends₁ : P₁ → V₁ × V₁}
  {ends₂ : P₂ → V₂ × V₂}
  {J₁ : P₁ → Real}
  {J₂ : P₂ → Real} :
-- imply
  multibondIsingPartition (multibondSumEnds ends₁ ends₂) (multibondSumCoupling J₁ J₂) = multibondIsingPartition ends₁ J₁ * multibondIsingPartition ends₂ J₂ := by
-- proof
  apply StatMech.FrontierA.multibondIsingPartition_sum ends₁ ends₂ J₁ J₂

/--
[multibondTwistCoupling_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean)
-/
@[path]
private lemma multibondTwistCoupling_sum_eq
  [Fintype P]
  [DecidableEq P]
  {J₁ : P₁ → Real}
  {J₂ : P₂ → Real}
  {D₁ : Finset P₁}
  {D₂ : Finset P₂} :
-- imply
  multibondTwistCoupling (multibondSumCoupling J₁ J₂) (multibondSumSheet D₁ D₂) = multibondSumCoupling (multibondTwistCoupling J₁ D₁) (multibondTwistCoupling J₂ D₂) := by
-- proof
  apply StatMech.FrontierA.multibondTwistCoupling_sum J₁ J₂ D₁ D₂

/--
[multibondDisorderFreeEnergy_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean)
-/
@[path]
private lemma multibondDisorderFreeEnergy_sum_eq
  [Fintype P]
  [DecidableEq P]
  {ends₁ : P₁ → V₁ × V₁}
  {ends₂ : P₂ → V₂ × V₂}
  {J₁ : P₁ → Real}
  {J₂ : P₂ → Real}
  {D₁ : Finset P₁}
  {D₂ : Finset P₂} :
-- imply
  multibondDisorderFreeEnergy (multibondSumEnds ends₁ ends₂) (multibondSumCoupling J₁ J₂) (multibondSumSheet D₁ D₂) = multibondDisorderFreeEnergy ends₁ J₁ D₁ + multibondDisorderFreeEnergy ends₂ J₂ D₂ := by
-- proof
  apply StatMech.FrontierA.multibondDisorderFreeEnergy_sum ends₁ ends₂ J₁ J₂ D₁ D₂

/--
[rootedSumAnchoredEquiv_symm_apply_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean)
-/
@[path]
private lemma rootedSumAnchoredEquiv_symm_apply_inl_eq
  [Fintype P]
  [DecidableEq P]
  {s₁ : AnchoredConfig (Option V₁) none}
  {s₂ : AnchoredConfig (Option V₂) none}
  {q : Option V₁} :
-- imply
  ((rootedSumAnchoredEquiv (V₁ := V₁) (V₂ := V₂)).symm (s₁, s₂)).1 (rootedSumInl q) = s₁.1 q := by
-- proof
  apply StatMech.FrontierA.rootedSumAnchoredEquiv_symm_apply_inl s₁ s₂ q

/--
[rootedSumAnchoredEquiv_symm_apply_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean)
-/
@[path]
private lemma rootedSumAnchoredEquiv_symm_apply_inr_eq
  [Fintype P]
  [DecidableEq P]
  {s₁ : AnchoredConfig (Option V₁) none}
  {s₂ : AnchoredConfig (Option V₂) none}
  {q : Option V₂} :
-- imply
  ((rootedSumAnchoredEquiv (V₁ := V₁) (V₂ := V₂)).symm (s₁, s₂)).1 (rootedSumInr q) = s₂.1 q := by
-- proof
  apply StatMech.FrontierA.rootedSumAnchoredEquiv_symm_apply_inr s₁ s₂ q

/--
[multibondIsingAction_rootedSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean)
-/
@[path]
private lemma multibondIsingAction_rootedSum_eq
  [Fintype P]
  [DecidableEq P]
  {ends₁ : P₁ → Option V₁ × Option V₁}
  {ends₂ : P₂ → Option V₂ × Option V₂}
  {J₁ : P₁ → Real}
  {J₂ : P₂ → Real}
  {s₁ : AnchoredConfig (Option V₁) none}
  {s₂ : AnchoredConfig (Option V₂) none} :
-- imply
  multibondIsingAction (multibondRootedSumEnds ends₁ ends₂) (multibondSumCoupling J₁ J₂) ((rootedSumAnchoredEquiv (V₁ := V₁) (V₂ := V₂)).symm (s₁, s₂)).1 = multibondIsingAction ends₁ J₁ s₁.1 + multibondIsingAction ends₂ J₂ s₂.1 := by
-- proof
  apply StatMech.FrontierA.multibondIsingAction_rootedSum ends₁ ends₂ J₁ J₂ s₁ s₂

/--
[multibondIsingWeight_rootedSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean)
-/
@[path]
private lemma multibondIsingWeight_rootedSum_eq
  [Fintype P]
  [DecidableEq P]
  {ends₁ : P₁ → Option V₁ × Option V₁}
  {ends₂ : P₂ → Option V₂ × Option V₂}
  {J₁ : P₁ → Real}
  {J₂ : P₂ → Real}
  {s₁ : AnchoredConfig (Option V₁) none}
  {s₂ : AnchoredConfig (Option V₂) none} :
-- imply
  multibondIsingWeight (multibondRootedSumEnds ends₁ ends₂) (multibondSumCoupling J₁ J₂) ((rootedSumAnchoredEquiv (V₁ := V₁) (V₂ := V₂)).symm (s₁, s₂)).1 = multibondIsingWeight ends₁ J₁ s₁.1 * multibondIsingWeight ends₂ J₂ s₂.1 := by
-- proof
  apply StatMech.FrontierA.multibondIsingWeight_rootedSum ends₁ ends₂ J₁ J₂ s₁ s₂

/--
[multibondIsingPartition_eq_two_mul_anchoredWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean)
-/
@[path]
private lemma multibondIsingPartition_eq_two_mul_anchoredWeight_eq
  [Fintype P]
  [DecidableEq P]
  [Fintype Q]
  [DecidableEq Q]
  [Fintype W]
  [DecidableEq W]
  {root : W}
  {ends : Q → W × W}
  {J : Q → Real} :
-- imply
  multibondIsingPartition ends J = 2 * ∑ s : AnchoredConfig W root, multibondIsingWeight ends J s.1 := by
-- proof
  apply StatMech.FrontierA.multibondIsingPartition_eq_two_mul_anchoredWeight root ends J

/--
[two_mul_multibondIsingPartition_rootedSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean)
-/
@[path]
private lemma two_mul_multibondIsingPartition_rootedSum_eq
  [Fintype P]
  [DecidableEq P]
  {ends₁ : P₁ → Option V₁ × Option V₁}
  {ends₂ : P₂ → Option V₂ × Option V₂}
  {J₁ : P₁ → Real}
  {J₂ : P₂ → Real} :
-- imply
  2 * multibondIsingPartition (multibondRootedSumEnds ends₁ ends₂) (multibondSumCoupling J₁ J₂) = multibondIsingPartition ends₁ J₁ * multibondIsingPartition ends₂ J₂ := by
-- proof
  apply StatMech.FrontierA.two_mul_multibondIsingPartition_rootedSum ends₁ ends₂ J₁ J₂

/--
[multibondDisorderFreeEnergy_rootedSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean)
-/
@[path]
private lemma multibondDisorderFreeEnergy_rootedSum_eq
  [Fintype P]
  [DecidableEq P]
  {ends₁ : P₁ → Option V₁ × Option V₁}
  {ends₂ : P₂ → Option V₂ × Option V₂}
  {J₁ : P₁ → Real}
  {J₂ : P₂ → Real}
  {D₁ : Finset P₁}
  {D₂ : Finset P₂} :
-- imply
  multibondDisorderFreeEnergy (multibondRootedSumEnds ends₁ ends₂) (multibondSumCoupling J₁ J₂) (multibondSumSheet D₁ D₂) = multibondDisorderFreeEnergy ends₁ J₁ D₁ + multibondDisorderFreeEnergy ends₂ J₂ D₂ := by
-- proof
  apply StatMech.FrontierA.multibondDisorderFreeEnergy_rootedSum ends₁ ends₂ J₁ J₂ D₁ D₂


-- created on 2026-10-23
