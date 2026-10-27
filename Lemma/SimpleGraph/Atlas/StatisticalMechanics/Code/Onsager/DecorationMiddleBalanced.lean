import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.DecorationMiddleBalanced
open StatMech StatMech.Onsager


/--
[ons_decMiddleBalanced_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleBalanced.lean)
-/
@[path]
private lemma ons_decMiddleBalanced_factor_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {omega t lambda : ℂ}
  {site : ZMod L × ZMod L} :
-- imply
  ons_decMiddleBalanced L decWeight omega t lambda site = ons_stateWeightedReversibleTurnMatrix ons_decMiddleAugDir omega (ons_decMiddleBalancedRowWeight decWeight lambda site) (ons_decMiddleBalancedColWeight decWeight t lambda) (ons_decMiddleInternalFactor L decWeight site) := by
-- proof
  apply StatMech.Onsager.ons_decMiddleBalanced_factor L decWeight omega t lambda site

/--
[ons_decMiddleBalanced_det](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleBalanced.lean)
-/
@[path]
private lemma ons_decMiddleBalanced_det_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {omega t lambda : ℂ}
  {site : ZMod L × ZMod L}
-- given
  (homega : omega ≠ 0)
  (hlambda : lambda ≠ 0) :
-- imply
  (1 - ons_decMiddleBalanced L decWeight omega t lambda site).det = (1 - ons_KWmatDecorationWeightedPhase L (ons_scaleDecEdgeWeight decWeight (ons_decChainEdge site 1) t) omega 1 1).det := by
-- proof
  apply StatMech.Onsager.ons_decMiddleBalanced_det L decWeight omega t lambda homega hlambda site

/--
[ons_loopWeight_decMiddleBalanced_eq_row](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleBalanced.lean)
-/
@[path]
private lemma ons_loopWeight_decMiddleBalanced_eq_row_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {decWeight : ons_DecEdge L → ℂ}
  {omega t lambda : ℂ}
  {site : ZMod L × ZMod L}
  {loop : Fin n → ons_Dart L ⊕ Fin 2}
-- given
  (hlambda : lambda ≠ 0) :
-- imply
  ons_loopWeight (ons_decMiddleBalanced L decWeight omega t lambda site) loop = ons_loopWeight (ons_decMiddleAugmented L decWeight omega 1 1 t site) loop := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_decMiddleBalanced_eq_row L decWeight omega t lambda hlambda site loop

/--
[ons_decMiddleBalanced_scaleColumns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleBalanced.lean)
-/
@[path]
private lemma ons_decMiddleBalanced_scaleColumns_eq
  {L : ℕ}
  {decWeight : ons_DecEdge L → ℂ}
  {omega t lambda : ℂ}
  {site : ZMod L × ZMod L} :
-- imply
  ons_decMiddleBalanced L decWeight omega t lambda site = ons_scaleColumns ({Sum.inr 0, Sum.inr 1} : Finset (ons_Dart L ⊕ Fin 2)) t (ons_decMiddleBalanced L decWeight omega 1 lambda site) := by
-- proof
  apply StatMech.Onsager.ons_decMiddleBalanced_scaleColumns L decWeight omega t lambda site

/--
[ons_decMiddleBalanced_lemma5](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleBalanced.lean)
-/
@[path]
private lemma ons_decMiddleBalanced_lemma5_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {decWeight : ons_DecEdge L → ℂ}
  {omega t lambda : ℂ}
  {site : ZMod L × ZMod L}
  {state : ons_Dart L ⊕ Fin 2}
-- given
  (homega : omega ≠ 0)
  (hI : omega ^ 2 = Complex.I)
  (hlambda : lambda ≠ 0) :
-- imply
  ∑ loop ∈ ons_loopSetBoth (n := n) state (ons_decMiddleAugRev L state), ons_loopWeight (ons_decMiddleBalanced L decWeight omega t lambda site) loop = 0 := by
-- proof
  apply StatMech.Onsager.ons_decMiddleBalanced_lemma5 L decWeight omega t lambda homega hI hlambda site state

/--
[ons_loopWeight_decMiddleBalanced_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleBalanced.lean)
-/
@[path]
private lemma ons_loopWeight_decMiddleBalanced_loopRev_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {decWeight : ons_DecEdge L → ℂ}
  {omega t lambda : ℂ}
  {site : ZMod L × ZMod L}
  {loop : Fin n → ons_Dart L ⊕ Fin 2}
-- given
  (homega : omega ≠ 0)
  (hI : omega ^ 2 = Complex.I)
  (hlambda : lambda ≠ 0) :
-- imply
  ons_loopWeight (ons_decMiddleBalanced L decWeight omega t lambda site) (ons_involutiveLoopRev (ons_decMiddleAugRev L) loop) = ons_loopWeight (ons_decMiddleBalanced L decWeight omega t lambda site) loop := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_decMiddleBalanced_loopRev L decWeight omega t lambda homega hI hlambda site loop

/--
[ons_detWalkRoot_decMiddleBalanced_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleBalanced.lean)
-/
@[path]
private lemma ons_detWalkRoot_decMiddleBalanced_affine_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {omega t lambda : ℂ}
  {site : ZMod L × ZMod L}
  {q : ℝ}
-- given
  (homega : omega ≠ 0)
  (hI : omega ^ 2 = Complex.I)
  (hlambda : lambda ≠ 0)
  (hq : 0 ≤ q)
  (hentry : ∀ x y, ‖ons_decMiddleBalanced L decWeight omega t lambda site x y‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card (ons_Dart L ⊕ Fin 2) : ℝ) ^ 2)⁻¹)
  (hcard : (Fintype.card (ons_Dart L ⊕ Fin 2) : ℝ) * q < 1) :
-- imply
  ons_detWalkRoot (ons_decMiddleBalanced L decWeight omega t lambda site) = ons_detWalkRoot (ons_maskMatrix ({Sum.inr 0, Sum.inr 1} : Finset (ons_Dart L ⊕ Fin 2)) (ons_decMiddleBalanced L decWeight omega 1 lambda site)) * (1 - t * ∑' s, ons_firstReturnWeight (ons_decMiddleBalanced L decWeight omega 1 lambda site) (Sum.inr 0) (Sum.inr 1) s) := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_decMiddleBalanced_affine L decWeight omega t lambda homega hI hlambda site q hq hentry hsmall hcard

/--
[norm_ons_decMiddleDestFactor_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleBalanced.lean)
-/
@[path]
private lemma norm_ons_decMiddleDestFactor_le_one_eq
  {L : ℕ}
  {decWeight : ons_DecEdge L → ℂ}
  {site : ZMod L × ZMod L}
  {mu : Fin 4}
-- given
  (hall : ∀ edge, ‖decWeight edge‖ ≤ 1) :
-- imply
  ‖ons_decMiddleDestFactor decWeight site mu‖ ≤ 1 := by
-- proof
  apply StatMech.Onsager.norm_ons_decMiddleDestFactor_le_one decWeight site hall mu

/--
[norm_ons_decMiddleSourceFactor_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleBalanced.lean)
-/
@[path]
private lemma norm_ons_decMiddleSourceFactor_le_one_eq
  {L : ℕ}
  {decWeight : ons_DecEdge L → ℂ}
  {site : ZMod L × ZMod L}
  {mu : Fin 4}
-- given
  (hall : ∀ edge, ‖decWeight edge‖ ≤ 1) :
-- imply
  ‖ons_decMiddleSourceFactor decWeight site mu‖ ≤ 1 := by
-- proof
  apply StatMech.Onsager.norm_ons_decMiddleSourceFactor_le_one decWeight site hall mu

/--
[norm_ons_decMiddleU_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleBalanced.lean)
-/
@[path]
private lemma norm_ons_decMiddleU_le_one_eq
  {L : ℕ}
  {decWeight : ons_DecEdge L → ℂ}
  {site : ZMod L × ZMod L}
  {d : ons_Dart L}
  {side : Fin 2}
-- given
  (hall : ∀ edge, ‖decWeight edge‖ ≤ 1) :
-- imply
  ‖ons_decMiddleU L decWeight ons_turnRoot site d side‖ ≤ 1 := by
-- proof
  apply StatMech.Onsager.norm_ons_decMiddleU_le_one L decWeight site hall d side

/--
[norm_ons_decMiddleV_le_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleBalanced.lean)
-/
@[path]
private lemma norm_ons_decMiddleV_le_sq_eq
  {L : ℕ}
  {decWeight : ons_DecEdge L → ℂ}
  {site : ZMod L × ZMod L}
  {r : ℝ}
  {side : Fin 2}
  {d : ons_Dart L}
-- given
  (hr0 : 0 ≤ r)
  (hr1 : r ≤ 1)
  (hall : ∀ edge, ‖decWeight edge‖ ≤ r) :
-- imply
  ‖ons_decMiddleV L decWeight ons_turnRoot 1 1 site side d‖ ≤ r ^ 2 := by
-- proof
  apply StatMech.Onsager.norm_ons_decMiddleV_le_sq L decWeight site r hr0 hr1 hall side d

/--
[norm_ons_decMiddleBalanced_entry_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleBalanced.lean)
-/
@[path]
private lemma norm_ons_decMiddleBalanced_entry_le_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {t lambda : ℂ}
  {site : ZMod L × ZMod L}
  {x y : ons_Dart L ⊕ Fin 2}
-- given
  (hlambda : lambda ≠ 0)
  (hlambdaOne : ‖lambda‖ ≤ 1)
  (ht : ‖t‖ ≤ 2)
  (hall : ∀ edge, ‖decWeight edge‖ ≤ ‖lambda‖) :
-- imply
  ‖ons_decMiddleBalanced L decWeight ons_turnRoot t lambda site x y‖ ≤ 2 * ‖lambda‖ := by
-- proof
  apply StatMech.Onsager.norm_ons_decMiddleBalanced_entry_le L decWeight t lambda hlambda site hlambdaOne ht hall x y

/--
[norm_ons_spinDartSeamSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleBalanced.lean)
-/
@[path]
private lemma norm_ons_spinDartSeamSign_eq
  {L : ℕ}
  {a b : Fin 2}
  {d : ons_Dart L} :
-- imply
  ‖ons_spinDartSeamSign a b d‖ = 1 := by
-- proof
  apply StatMech.Onsager.norm_ons_spinDartSeamSign a b d

/--
[norm_ons_spinSeamDecWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleBalanced.lean)
-/
@[path]
private lemma norm_ons_spinSeamDecWeight_eq
  {L : ℕ}
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {edge : ons_DecEdge L} :
-- imply
  ‖ons_spinSeamDecWeight decWeight a b edge‖ = ‖decWeight edge‖ := by
-- proof
  apply StatMech.Onsager.norm_ons_spinSeamDecWeight decWeight a b edge

/--
[ons_detWalkRoot_KWDecoration_spinGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleBalanced.lean)
-/
@[path]
private lemma ons_detWalkRoot_KWDecoration_spinGauge_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {omega : ℂ} :
-- imply
  ons_detWalkRoot (ons_KWmatDecorationWeightedPhase L decWeight omega (ons_spinPhase L a) (ons_spinPhase L b)) = ons_detWalkRoot (ons_KWmatDecorationWeightedPhase L (ons_spinSeamDecWeight decWeight a b) omega 1 1) := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_KWDecoration_spinGauge L decWeight a b omega

/--
[ons_detWalkRoot_scaleMiddle_balanced_affine_of_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleBalanced.lean)
-/
@[path]
private lemma ons_detWalkRoot_scaleMiddle_balanced_affine_of_bounds_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {t lambda : ℂ}
  {site : ZMod L × ZMod L}
  {qCompressed qAugmented : ℝ}
-- given
  (hlambda : lambda ≠ 0)
  (hqCompressed : 0 ≤ qCompressed)
  (hqAugmented : 0 ≤ qAugmented)
  (hentryCompressed : ∀ x y, ‖ons_KWmatDecorationWeightedPhase L (ons_spinSeamDecWeight (ons_scaleDecEdgeWeight decWeight (ons_decChainEdge site 1) t) a b) ons_turnRoot 1 1 x y‖ ≤ qCompressed)
  (hentryAugmented : ∀ x y, ‖ons_decMiddleBalanced L (ons_spinSeamDecWeight decWeight a b) ons_turnRoot t lambda site x y‖ ≤ qAugmented)
  (hsmallCompressed : qCompressed < (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹)
  (hsmallAugmented : qAugmented < (2 * (Fintype.card (ons_Dart L ⊕ Fin 2) : ℝ) ^ 2)⁻¹) :
-- imply
  ons_detWalkRoot (ons_KWmatDecorationWeightedPhase L (ons_scaleDecEdgeWeight decWeight (ons_decChainEdge site 1) t) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) = ons_detWalkRoot (ons_maskMatrix ({Sum.inr 0, Sum.inr 1} : Finset (ons_Dart L ⊕ Fin 2)) (ons_decMiddleBalanced L (ons_spinSeamDecWeight decWeight a b) ons_turnRoot 1 lambda site)) * (1 - t * ∑' s, ons_firstReturnWeight (ons_decMiddleBalanced L (ons_spinSeamDecWeight decWeight a b) ons_turnRoot 1 lambda site) (Sum.inr 0) (Sum.inr 1) s) := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_scaleMiddle_balanced_affine_of_bounds L decWeight a b t lambda hlambda site qCompressed qAugmented hqCompressed hqAugmented hentryCompressed hentryAugmented hsmallCompressed hsmallAugmented


-- created on 2026-10-23
