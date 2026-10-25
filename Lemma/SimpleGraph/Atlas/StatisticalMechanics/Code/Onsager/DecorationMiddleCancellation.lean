import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.DecorationMiddleCancellation
open StatMech StatMech.Onsager


/--
[ons_decMiddleAugRev_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleCancellation.lean)
-/
@[path]
private lemma ons_decMiddleAugRev_involutive_eq
  {L : ℕ} :
-- imply
  Function.Involutive (ons_decMiddleAugRev L) := by
-- proof
  apply StatMech.Onsager.ons_decMiddleAugRev_involutive L

/--
[ons_decMiddleAugDir_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleCancellation.lean)
-/
@[path]
private lemma ons_decMiddleAugDir_rev_eq
  {L : ℕ}
  {state : ons_Dart L ⊕ Fin 2} :
-- imply
  ons_decMiddleAugDir (ons_decMiddleAugRev L state) = ons_decMiddleAugDir state + 2 := by
-- proof
  apply StatMech.Onsager.ons_decMiddleAugDir_rev L state

/--
[ons_decMiddleAugRev_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleCancellation.lean)
-/
@[path]
private lemma ons_decMiddleAugRev_ne_eq
  {L : ℕ}
  [Fact (2 < L)]
  {state : ons_Dart L ⊕ Fin 2} :
-- imply
  ons_decMiddleAugRev L state ≠ state := by
-- proof
  apply StatMech.Onsager.ons_decMiddleAugRev_ne L state

/--
[ons_scaleMiddle_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleCancellation.lean)
-/
@[path]
private lemma ons_scaleMiddle_external_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {site : ZMod L × ZMod L}
  {t : ℂ}
  {d : ons_Dart L} :
-- imply
  ons_scaleDecEdgeWeight decWeight (ons_decChainEdge site 1) t s(d, ons_dartRev L d) = decWeight s(d, ons_dartRev L d) := by
-- proof
  apply StatMech.Onsager.ons_scaleMiddle_external L decWeight site t d

/--
[ons_decMiddleStateWeight_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleCancellation.lean)
-/
@[path]
private lemma ons_decMiddleStateWeight_rev_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {t : ℂ}
  {site : ZMod L × ZMod L}
  {state : ons_Dart L ⊕ Fin 2} :
-- imply
  ons_decMiddleRowWeight decWeight t site (ons_decMiddleAugRev L state) * ons_decMiddleColWeight decWeight (ons_decMiddleAugRev L state) = ons_decMiddleRowWeight decWeight t site state * ons_decMiddleColWeight decWeight state := by
-- proof
  apply StatMech.Onsager.ons_decMiddleStateWeight_rev L decWeight t site state

/--
[ons_decMiddleInternalFactor_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleCancellation.lean)
-/
@[path]
private lemma ons_decMiddleInternalFactor_rev_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {site : ZMod L × ZMod L}
  {x y : ons_Dart L ⊕ Fin 2} :
-- imply
  ons_decMiddleInternalFactor L decWeight site (ons_decMiddleAugRev L y) (ons_decMiddleAugRev L x) = ons_decMiddleInternalFactor L decWeight site x y := by
-- proof
  apply StatMech.Onsager.ons_decMiddleInternalFactor_rev L decWeight site x y

/--
[ons_decMiddleAugmented_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleCancellation.lean)
-/
@[path]
private lemma ons_decMiddleAugmented_factor_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {omega t : ℂ}
  {site : ZMod L × ZMod L} :
-- imply
  ons_decMiddleAugmented L decWeight omega 1 1 t site = ons_stateWeightedReversibleTurnMatrix ons_decMiddleAugDir omega (ons_decMiddleRowWeight decWeight t site) (ons_decMiddleColWeight decWeight) (ons_decMiddleInternalFactor L decWeight site) := by
-- proof
  apply StatMech.Onsager.ons_decMiddleAugmented_factor L decWeight omega t site

/--
[ons_decMiddleAugmented_lemma5](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleCancellation.lean)
-/
@[path]
private lemma ons_decMiddleAugmented_lemma5_eq
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
  ∑ loop ∈ ons_loopSetBoth (n := n) state (ons_decMiddleAugRev L state), ons_loopWeight (ons_decMiddleAugmented L decWeight omega 1 1 t site) loop = 0 := by
-- proof
  apply StatMech.Onsager.ons_decMiddleAugmented_lemma5 L decWeight omega t homega hI site state

/--
[ons_loopWeight_decMiddleAugmented_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleCancellation.lean)
-/
@[path]
private lemma ons_loopWeight_decMiddleAugmented_loopRev_eq
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
  ons_loopWeight (ons_decMiddleAugmented L decWeight omega 1 1 t site) (ons_involutiveLoopRev (ons_decMiddleAugRev L) loop) = ons_loopWeight (ons_decMiddleAugmented L decWeight omega 1 1 t site) loop := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_decMiddleAugmented_loopRev L decWeight omega t homega hI site loop

/--
[ons_decMiddleAugmented_mask_lemma5](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleCancellation.lean)
-/
@[path]
private lemma ons_decMiddleAugmented_mask_lemma5_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {decWeight : ons_DecEdge L → ℂ}
  {omega t : ℂ}
  {site : ZMod L × ZMod L}
  {forbidden : Finset (ons_Dart L ⊕ Fin 2)}
  {state : ons_Dart L ⊕ Fin 2}
-- given
  (homega : omega ≠ 0)
  (hI : omega ^ 2 = Complex.I)
  (hforbidden : ∀ state, ons_decMiddleAugRev L state ∈ forbidden ↔ state ∈ forbidden) :
-- imply
  ∑ loop ∈ ons_loopSetBoth (n := n) state (ons_decMiddleAugRev L state), ons_loopWeight (ons_maskMatrix forbidden (ons_decMiddleAugmented L decWeight omega 1 1 t site)) loop = 0 := by
-- proof
  apply StatMech.Onsager.ons_decMiddleAugmented_mask_lemma5 L decWeight omega t homega hI site forbidden hforbidden state

/--
[ons_loopWeight_decMiddleAugmented_mask_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationMiddleCancellation.lean)
-/
@[path]
private lemma ons_loopWeight_decMiddleAugmented_mask_loopRev_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {decWeight : ons_DecEdge L → ℂ}
  {omega t : ℂ}
  {site : ZMod L × ZMod L}
  {forbidden : Finset (ons_Dart L ⊕ Fin 2)}
  {loop : Fin n → ons_Dart L ⊕ Fin 2}
-- given
  (homega : omega ≠ 0)
  (hI : omega ^ 2 = Complex.I)
  (hforbidden : ∀ state, ons_decMiddleAugRev L state ∈ forbidden ↔ state ∈ forbidden) :
-- imply
  ons_loopWeight (ons_maskMatrix forbidden (ons_decMiddleAugmented L decWeight omega 1 1 t site)) (ons_involutiveLoopRev (ons_decMiddleAugRev L) loop) = ons_loopWeight (ons_maskMatrix forbidden (ons_decMiddleAugmented L decWeight omega 1 1 t site)) loop := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_decMiddleAugmented_mask_loopRev L decWeight omega t homega hI site forbidden hforbidden loop


-- created on 2026-10-23
