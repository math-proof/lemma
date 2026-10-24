import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.DecorationExternalDeletion
open StatMech StatMech.Onsager


/--
[ons_scaleDecEdgeWeight_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationExternalDeletion.lean)
-/
@[path]
private lemma ons_scaleDecEdgeWeight_external_eq
  {L : ℕ}
  {decWeight : ons_DecEdge L → ℂ}
  {t : ℂ}
  {e : ons_Dart L} :
-- imply
  ons_scaleDecEdgeWeight decWeight s(e, ons_dartRev L e) t s(e, ons_dartRev L e) = t * decWeight s(e, ons_dartRev L e) := by
-- proof
  apply StatMech.Onsager.ons_scaleDecEdgeWeight_external L decWeight t e

/--
[ons_scaleDecEdgeWeight_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationExternalDeletion.lean)
-/
@[path]
private lemma ons_scaleDecEdgeWeight_chain_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {t : ℂ}
  {e : ons_Dart L}
  {site : ZMod L × ZMod L}
  {i : Fin 3} :
-- imply
  ons_scaleDecEdgeWeight decWeight s(e, ons_dartRev L e) t (ons_decChainEdge site i) = decWeight (ons_decChainEdge site i) := by
-- proof
  apply StatMech.Onsager.ons_scaleDecEdgeWeight_chain L decWeight t e site i

/--
[ons_decTransitionWeight_scaleExternal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationExternalDeletion.lean)
-/
@[path]
private lemma ons_decTransitionWeight_scaleExternal_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {t : ℂ}
  {e d₂ d₁ : ons_Dart L} :
-- imply
  ons_decTransitionWeight L (ons_scaleDecEdgeWeight decWeight s(e, ons_dartRev L e) t) d₂ d₁ = if d₁ = e ∨ d₁ = ons_dartRev L e then t * ons_decTransitionWeight L decWeight d₂ d₁ else ons_decTransitionWeight L decWeight d₂ d₁ := by
-- proof
  apply StatMech.Onsager.ons_decTransitionWeight_scaleExternal L decWeight t e d₂ d₁

/--
[ons_KWmatDecorationWeightedPhase_scaleExternal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationExternalDeletion.lean)
-/
@[path]
private lemma ons_KWmatDecorationWeightedPhase_scaleExternal_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {omega u v t : ℂ}
  {e : ons_Dart L} :
-- imply
  ons_KWmatDecorationWeightedPhase L (ons_scaleDecEdgeWeight decWeight s(e, ons_dartRev L e) t) omega u v = ons_scaleColumns ({e, ons_dartRev L e} : Finset (ons_Dart L)) t (ons_KWmatDecorationWeightedPhase L decWeight omega u v) := by
-- proof
  apply StatMech.Onsager.ons_KWmatDecorationWeightedPhase_scaleExternal L decWeight omega u v t e

/--
[ons_decLoopSum_both_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationExternalDeletion.lean)
-/
@[path]
private lemma ons_decLoopSum_both_zero_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {e : ons_Dart L} :
-- imply
  (∑ loop ∈ (Finset.univ : Finset (Fin (n + 1) → ons_Dart L)).filter (fun loop => (∃ i, loop i = e) ∧ ∃ j, loop j = ons_dartRev L e), ons_loopWeight (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) loop) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decLoopSum_both_zero L n decWeight a b e

/--
[ons_decMaskLoopSum_both_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationExternalDeletion.lean)
-/
@[path]
private lemma ons_decMaskLoopSum_both_zero_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {forbidden : Finset (ons_Dart L)}
  {e : ons_Dart L}
-- given
  (hforbidden : ∀ d, ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden) :
-- imply
  (∑ loop ∈ (Finset.univ : Finset (Fin (n + 1) → ons_Dart L)).filter (fun loop => (∃ i, loop i = e) ∧ ∃ j, loop j = ons_dartRev L e), ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b))) loop) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decMaskLoopSum_both_zero L n decWeight a b forbidden hforbidden e

/--
[ons_decLoopSum_orientation_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationExternalDeletion.lean)
-/
@[path]
private lemma ons_decLoopSum_orientation_symm_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {e : ons_Dart L} :
-- imply
  (∑ loop ∈ Finset.univ.filter (fun loop : Fin n → ons_Dart L => (∃ i, loop i = e) ∧ ¬ ∃ j, loop j = ons_dartRev L e), ons_loopWeight (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) loop) = ∑ loop ∈ Finset.univ.filter (fun loop : Fin n → ons_Dart L => (∃ i, loop i = ons_dartRev L e) ∧ ¬ ∃ j, loop j = e), ons_loopWeight (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) loop := by
-- proof
  apply StatMech.Onsager.ons_decLoopSum_orientation_symm L decWeight a b e

/--
[ons_decMaskLoopSum_orientation_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationExternalDeletion.lean)
-/
@[path]
private lemma ons_decMaskLoopSum_orientation_symm_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {forbidden : Finset (ons_Dart L)}
  {e : ons_Dart L}
-- given
  (hforbidden : ∀ d, ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden) :
-- imply
  (∑ loop ∈ Finset.univ.filter (fun loop : Fin n → ons_Dart L => (∃ i, loop i = e) ∧ ¬ ∃ j, loop j = ons_dartRev L e), ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b))) loop) = ∑ loop ∈ Finset.univ.filter (fun loop : Fin n → ons_Dart L => (∃ i, loop i = ons_dartRev L e) ∧ ¬ ∃ j, loop j = e), ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b))) loop := by
-- proof
  apply StatMech.Onsager.ons_decMaskLoopSum_orientation_symm L decWeight a b forbidden hforbidden e

/--
[ons_decLoopSum_two_bucket](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationExternalDeletion.lean)
-/
@[path]
private lemma ons_decLoopSum_two_bucket_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {e : ons_Dart L} :
-- imply
  (∑ loop : Fin (n + 1) → ons_Dart L, ons_loopWeight (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) loop) = 2 * ons_decPhaseBucketE L decWeight a b e n + ons_decPhaseBucketN L decWeight a b e n := by
-- proof
  apply StatMech.Onsager.ons_decLoopSum_two_bucket L decWeight a b e

/--
[ons_decMaskLoopSum_two_bucket](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationExternalDeletion.lean)
-/
@[path]
private lemma ons_decMaskLoopSum_two_bucket_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {forbidden : Finset (ons_Dart L)}
  {e : ons_Dart L}
-- given
  (hforbidden : ∀ d, ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden) :
-- imply
  (∑ loop : Fin (n + 1) → ons_Dart L, ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b))) loop) = 2 * ons_decMaskPhaseBucketE L decWeight a b forbidden e n + ons_decMaskPhaseBucketN L decWeight a b forbidden e n := by
-- proof
  apply StatMech.Onsager.ons_decMaskLoopSum_two_bucket L decWeight a b forbidden hforbidden e

/--
[ons_detWalkRoot_decoration_mask_delete_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationExternalDeletion.lean)
-/
@[path]
private lemma ons_detWalkRoot_decoration_mask_delete_pair_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {q : ℝ}
  {forbidden : Finset (ons_Dart L)}
  {e : ons_Dart L}
-- given
  (hq : 0 ≤ q)
  (hentryM : ∀ d₂ d₁, ‖ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) d₂ d₁‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹)
  (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1)
  (hforbidden : ∀ d, ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden) :
-- imply
  ons_detWalkRoot (ons_maskMatrix forbidden (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b))) = ons_detWalkRoot (ons_maskMatrix (({e, ons_dartRev L e} : Finset (ons_Dart L)) ∪ forbidden) (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b))) * (1 - ∑' s, ons_firstReturnWeight (ons_maskMatrix forbidden (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b))) e (ons_dartRev L e) s) := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_decoration_mask_delete_pair L decWeight a b q hq hentryM hsmall hcard forbidden hforbidden e

/--
[ons_detWalkRoot_decoration_scaleExternal_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationExternalDeletion.lean)
-/
@[path]
private lemma ons_detWalkRoot_decoration_scaleExternal_affine_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {q : ℝ}
  {t : ℂ}
  {e : ons_Dart L}
-- given
  (hq : 0 ≤ q)
  (hentryScaled : ∀ d₂ d₁, ‖ons_KWmatDecorationWeightedPhase L (ons_scaleDecEdgeWeight decWeight s(e, ons_dartRev L e) t) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) d₂ d₁‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹)
  (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1) :
-- imply
  ons_detWalkRoot (ons_KWmatDecorationWeightedPhase L (ons_scaleDecEdgeWeight decWeight s(e, ons_dartRev L e) t) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) = ons_detWalkRoot (ons_maskMatrix ({e, ons_dartRev L e} : Finset (ons_Dart L)) (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b))) * (1 - t * ∑' s, ons_firstReturnWeight (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) e (ons_dartRev L e) s) := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_decoration_scaleExternal_affine L decWeight a b q hq t e hentryScaled hsmall hcard


-- created on 2026-10-23
