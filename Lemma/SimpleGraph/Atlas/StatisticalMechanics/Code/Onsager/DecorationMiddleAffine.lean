import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.DecorationMiddleAffine
open StatMech StatMech.Onsager


/--
[ons_decMiddleAugmentedCol_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleAffine.lean)
-/
@[path]
private lemma ons_decMiddleAugmentedCol_factor_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {omega t : ℂ}
  {site : ZMod L × ZMod L} :
-- imply
  ons_decMiddleAugmentedCol L decWeight omega t site = ons_stateWeightedReversibleTurnMatrix ons_decMiddleAugDir omega (ons_decMiddleColRowWeight decWeight site) (ons_decMiddleColColWeight decWeight t) (ons_decMiddleInternalFactor L decWeight site) := by
-- proof
  apply StatMech.Onsager.ons_decMiddleAugmentedCol_factor L decWeight omega t site

/--
[ons_decMiddleAugmentedCol_det](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleAffine.lean)
-/
@[path]
private lemma ons_decMiddleAugmentedCol_det_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {omega t : ℂ}
  {site : ZMod L × ZMod L}
-- given
  (homega : omega ≠ 0) :
-- imply
  (1 - ons_decMiddleAugmentedCol L decWeight omega t site).det = (1 - ons_KWmatDecorationWeightedPhase L (ons_scaleDecEdgeWeight decWeight (ons_decChainEdge site 1) t) omega 1 1).det := by
-- proof
  apply StatMech.Onsager.ons_decMiddleAugmentedCol_det L decWeight omega t homega site

/--
[ons_loopWeight_decMiddleAugmentedCol_eq_row](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleAffine.lean)
-/
@[path]
private lemma ons_loopWeight_decMiddleAugmentedCol_eq_row_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {decWeight : ons_DecEdge L → ℂ}
  {omega t : ℂ}
  {site : ZMod L × ZMod L}
  {loop : Fin n → ons_Dart L ⊕ Fin 2} :
-- imply
  ons_loopWeight (ons_decMiddleAugmentedCol L decWeight omega t site) loop = ons_loopWeight (ons_decMiddleAugmented L decWeight omega 1 1 t site) loop := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_decMiddleAugmentedCol_eq_row L decWeight omega t site loop

/--
[ons_decMiddleAugmentedCol_scaleColumns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleAffine.lean)
-/
@[path]
private lemma ons_decMiddleAugmentedCol_scaleColumns_eq
  {L : ℕ}
  {decWeight : ons_DecEdge L → ℂ}
  {omega t : ℂ}
  {site : ZMod L × ZMod L} :
-- imply
  ons_decMiddleAugmentedCol L decWeight omega t site = ons_scaleColumns ({Sum.inr 0, Sum.inr 1} : Finset (ons_Dart L ⊕ Fin 2)) t (ons_decMiddleAugmentedCol L decWeight omega 1 site) := by
-- proof
  apply StatMech.Onsager.ons_decMiddleAugmentedCol_scaleColumns L decWeight omega t site

/--
[ons_decMiddleAugmentedCol_lemma5](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleAffine.lean)
-/
@[path]
private lemma ons_decMiddleAugmentedCol_lemma5_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {decWeight : ons_DecEdge L → ℂ}
  {omega t : ℂ}
  {site : ZMod L × ZMod L}
  {state : ons_Dart L ⊕ Fin 2}
-- given
  (homega : omega ≠ 0)
  (hI : omega ^ 2 = Complex.I) :
-- imply
  ∑ loop ∈ ons_loopSetBoth (n := n) state (ons_decMiddleAugRev L state), ons_loopWeight (ons_decMiddleAugmentedCol L decWeight omega t site) loop = 0 := by
-- proof
  apply StatMech.Onsager.ons_decMiddleAugmentedCol_lemma5 L decWeight omega t homega hI site state

/--
[ons_loopWeight_decMiddleAugmentedCol_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleAffine.lean)
-/
@[path]
private lemma ons_loopWeight_decMiddleAugmentedCol_loopRev_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {decWeight : ons_DecEdge L → ℂ}
  {omega t : ℂ}
  {site : ZMod L × ZMod L}
  {loop : Fin n → ons_Dart L ⊕ Fin 2}
-- given
  (homega : omega ≠ 0)
  (hI : omega ^ 2 = Complex.I) :
-- imply
  ons_loopWeight (ons_decMiddleAugmentedCol L decWeight omega t site) (ons_involutiveLoopRev (ons_decMiddleAugRev L) loop) = ons_loopWeight (ons_decMiddleAugmentedCol L decWeight omega t site) loop := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_decMiddleAugmentedCol_loopRev L decWeight omega t homega hI site loop

/--
[ons_detWalkRoot_decMiddleAugmentedCol_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleAffine.lean)
-/
@[path]
private lemma ons_detWalkRoot_decMiddleAugmentedCol_affine_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {omega t : ℂ}
  {site : ZMod L × ZMod L}
  {q : ℝ}
-- given
  (homega : omega ≠ 0)
  (hI : omega ^ 2 = Complex.I)
  (hq : 0 ≤ q)
  (hentry : ∀ x y, ‖ons_decMiddleAugmentedCol L decWeight omega t site x y‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card (ons_Dart L ⊕ Fin 2) : ℝ) ^ 2)⁻¹)
  (hcard : (Fintype.card (ons_Dart L ⊕ Fin 2) : ℝ) * q < 1) :
-- imply
  ons_detWalkRoot (ons_decMiddleAugmentedCol L decWeight omega t site) = ons_detWalkRoot (ons_maskMatrix ({Sum.inr 0, Sum.inr 1} : Finset (ons_Dart L ⊕ Fin 2)) (ons_decMiddleAugmentedCol L decWeight omega 1 site)) * (1 - t * ∑' s, ons_firstReturnWeight (ons_decMiddleAugmentedCol L decWeight omega 1 site) (Sum.inr 0) (Sum.inr 1) s) := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_decMiddleAugmentedCol_affine L decWeight omega t homega hI site q hq hentry hsmall hcard

/--
[ons_detWalkRoot_decMiddleAugmented_spinGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleAffine.lean)
-/
@[path]
private lemma ons_detWalkRoot_decMiddleAugmented_spinGauge_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {omega t : ℂ}
  {site : ZMod L × ZMod L} :
-- imply
  ons_detWalkRoot (ons_decMiddleAugmented L decWeight omega (ons_spinPhase L a) (ons_spinPhase L b) t site) = ons_detWalkRoot (ons_decMiddleAugmented L (ons_spinSeamDecWeight decWeight a b) omega 1 1 t site) := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_decMiddleAugmented_spinGauge L decWeight a b omega t site

/--
[ons_detWalkRoot_decMiddleAugmented_row_eq_col](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleAffine.lean)
-/
@[path]
private lemma ons_detWalkRoot_decMiddleAugmented_row_eq_col_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {omega t : ℂ}
  {site : ZMod L × ZMod L} :
-- imply
  ons_detWalkRoot (ons_decMiddleAugmented L decWeight omega 1 1 t site) = ons_detWalkRoot (ons_decMiddleAugmentedCol L decWeight omega t site) := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_decMiddleAugmented_row_eq_col L decWeight omega t site

/--
[ons_detWalkRoot_scaleMiddle_affine_of_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleAffine.lean)
-/
@[path]
private lemma ons_detWalkRoot_scaleMiddle_affine_of_bounds_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {omega t : ℂ}
  {site : ZMod L × ZMod L}
  {qCompressed qAugmented : ℝ}
-- given
  (homega : omega ≠ 0)
  (hI : omega ^ 2 = Complex.I)
  (hqCompressed : 0 ≤ qCompressed)
  (hqAugmented : 0 ≤ qAugmented)
  (hentryCompressed : ∀ x y, ‖ons_KWmatDecorationWeightedPhase L (ons_scaleDecEdgeWeight decWeight (ons_decChainEdge site 1) t) omega (ons_spinPhase L a) (ons_spinPhase L b) x y‖ ≤ qCompressed)
  (hentryAugmentedRow : ∀ x y, ‖ons_decMiddleAugmented L decWeight omega (ons_spinPhase L a) (ons_spinPhase L b) t site x y‖ ≤ qAugmented)
  (hentryAugmentedCol : ∀ x y, ‖ons_decMiddleAugmentedCol L (ons_spinSeamDecWeight decWeight a b) omega t site x y‖ ≤ qAugmented)
  (hsmallCompressed : qCompressed < (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹)
  (hsmallAugmented : qAugmented < (2 * (Fintype.card (ons_Dart L ⊕ Fin 2) : ℝ) ^ 2)⁻¹) :
-- imply
  ons_detWalkRoot (ons_KWmatDecorationWeightedPhase L (ons_scaleDecEdgeWeight decWeight (ons_decChainEdge site 1) t) omega (ons_spinPhase L a) (ons_spinPhase L b)) = ons_detWalkRoot (ons_maskMatrix ({Sum.inr 0, Sum.inr 1} : Finset (ons_Dart L ⊕ Fin 2)) (ons_decMiddleAugmentedCol L (ons_spinSeamDecWeight decWeight a b) omega 1 site)) * (1 - t * ∑' s, ons_firstReturnWeight (ons_decMiddleAugmentedCol L (ons_spinSeamDecWeight decWeight a b) omega 1 site) (Sum.inr 0) (Sum.inr 1) s) := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_scaleMiddle_affine_of_bounds L decWeight a b omega t homega hI site qCompressed qAugmented hqCompressed hqAugmented hentryCompressed hentryAugmentedRow hentryAugmentedCol hsmallCompressed hsmallAugmented


-- created on 2026-10-23
