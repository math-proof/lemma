import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTranslationClosure.Part9
open MeasureTheory SimpleGraph Set StatMech StatMech.BeffaraDC


/--
[translateConfig_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma translateConfig_add_eq
  {t s : Site 2}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  translateConfig t (translateConfig s omega) = translateConfig (t + s) omega := by
-- proof
  apply StatMech.BeffaraDC.translateConfig_add t s omega

/--
[torusAmbientTranslateConfig_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma torusAmbientTranslateConfig_add_eq
  {L : ℕ}
  [Fact (2 < L)]
  {t s : Site 2}
  {omega : TorusAmbientConfig L} :
-- imply
  torusAmbientTranslateConfig L t (torusAmbientTranslateConfig L s omega) = torusAmbientTranslateConfig L (t + s) omega := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientTranslateConfig_add L t s omega

/--
[torusAmbientTranslateConfig_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma torusAmbientTranslateConfig_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L} :
-- imply
  torusAmbientTranslateConfig L 0 omega = omega := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientTranslateConfig_zero L omega

/--
[bdcTorusThinCrossing_subset_translationClosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma bdcTorusThinCrossing_subset_translationClosure_eq
  {L alpha n : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L}
-- given
  (h : bdcTorusThinCrossing L alpha n omega) :
-- imply
  bdcTorusThinCrossingTranslationClosure L alpha n omega := by
-- proof
  apply StatMech.BeffaraDC.bdcTorusThinCrossing_subset_translationClosure L alpha n omega h

/--
[bdcTorusThinCrossingTranslationClosure_translate_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma bdcTorusThinCrossingTranslationClosure_translate_iff_eq
  {L alpha n : ℕ}
  [Fact (2 < L)]
  {s : Site 2}
  {omega : TorusAmbientConfig L} :
-- imply
  bdcTorusThinCrossingTranslationClosure L alpha n (torusAmbientTranslateConfig L s omega) ↔ bdcTorusThinCrossingTranslationClosure L alpha n omega := by
-- proof
  apply StatMech.BeffaraDC.bdcTorusThinCrossingTranslationClosure_translate_iff L alpha n s omega

/--
[bdcTorusThinCrossingTranslationClosureEvent_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma bdcTorusThinCrossingTranslationClosureEvent_preimage_eq
  {L alpha n : ℕ}
  [Fact (2 < L)]
  {s : Site 2} :
-- imply
  torusAmbientTranslateConfig L s ⁻¹' bdcTorusThinCrossingTranslationClosureEvent L alpha n = bdcTorusThinCrossingTranslationClosureEvent L alpha n := by
-- proof
  apply StatMech.BeffaraDC.bdcTorusThinCrossingTranslationClosureEvent_preimage L alpha n s

/--
[torusReduceSite_bdcTorusCanonicalShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma torusReduceSite_bdcTorusCanonicalShift_eq
  {L : ℕ}
  [NeZero L]
  {u : ZMod L × ZMod L} :
-- imply
  torusReduceSite L (bdcTorusCanonicalShift u) = u := by
-- proof
  apply StatMech.BeffaraDC.torusReduceSite_bdcTorusCanonicalShift L u

/--
[torusAmbientTranslateConfig_eq_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma torusAmbientTranslateConfig_eq_canonical_eq
  {L : ℕ}
  [Fact (2 < L)]
  {t : Site 2}
  {omega : TorusAmbientConfig L} :
-- imply
  torusAmbientTranslateConfig L t omega = torusAmbientTranslateConfig L (bdcTorusCanonicalShift (torusReduceSite L t)) omega := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientTranslateConfig_eq_canonical L t omega

/--
[bdcLongRectangleTorusTranslationIndex_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma bdcLongRectangleTorusTranslationIndex_card_eq
  {L alpha : ℕ}
  [NeZero L] :
-- imply
  Fintype.card (BdcLongRectangleTorusTranslationIndex L alpha) = L ^ 2 * (2 * alpha ^ 3) := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangleTorusTranslationIndex_card L alpha

/--
[bdcLongRectangleTorusTranslationIndices_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma bdcLongRectangleTorusTranslationIndices_card_eq
  {L alpha : ℕ}
  [NeZero L] :
-- imply
  (bdcLongRectangleTorusTranslationIndices L alpha).card = L ^ 2 * (2 * alpha ^ 3) := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangleTorusTranslationIndices_card L alpha

/--
[monotone_translateConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma monotone_translateConfig_eq
  {t : Site 2} :
-- imply
  Monotone (translateConfig t) := by
-- proof
  apply StatMech.BeffaraDC.monotone_translateConfig t

/--
[bdcLongRectangleTorusTranslatedEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma bdcLongRectangleTorusTranslatedEvent_isIncreasing_eq
  {L alpha n : ℕ}
  {j : BdcLongRectangleTorusTranslationIndex L alpha} :
-- imply
  IsIncreasing (bdcLongRectangleTorusTranslatedEvent L alpha n j) := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangleTorusTranslatedEvent_isIncreasing L alpha n j

/--
[bdcLongRectangleTorusTranslatedEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma bdcLongRectangleTorusTranslatedEvent_measurableSet_eq
  {L alpha n : ℕ}
  {j : BdcLongRectangleTorusTranslationIndex L alpha} :
-- imply
  MeasurableSet (bdcLongRectangleTorusTranslatedEvent L alpha n j) := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangleTorusTranslatedEvent_measurableSet L alpha n j

/--
[bdcLongRectangleTorusTranslatedEvent_probability_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma bdcLongRectangleTorusTranslatedEvent_probability_eq_eq
  {mu : Measure (ConfigSpace (Sym2 (Site 2)))}
  {L alpha n : ℕ}
  {j : BdcLongRectangleTorusTranslationIndex L alpha}
-- given
  (hshift : ∀ t : Site 2, MeasurePreserving (translateConfig t) mu mu) :
-- imply
  mu.real (bdcLongRectangleTorusTranslatedEvent L alpha n j) = mu.real (bdcLongRectangleBaseEvent alpha n) := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangleTorusTranslatedEvent_probability_eq mu hshift L alpha n j

/--
[bdcLongRectangleTorusTranslationExpandedUnion_eq_finset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma bdcLongRectangleTorusTranslationExpandedUnion_eq_finset_eq
  {L alpha n : ℕ}
  [NeZero L] :
-- imply
  bdcLongRectangleTorusTranslationExpandedUnion L alpha n = ⋃ j ∈ bdcLongRectangleTorusTranslationIndices L alpha, bdcLongRectangleTorusTranslatedEvent L alpha n j := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangleTorusTranslationExpandedUnion_eq_finset L alpha n

/--
[bdcLongRectangleTorusTranslationOriginIndex_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma bdcLongRectangleTorusTranslationOriginIndex_mem_eq
  {L alpha : ℕ}
  [NeZero L]
-- given
  (ha : 0 < alpha) :
-- imply
  bdcLongRectangleTorusTranslationOriginIndex L alpha ha ∈ bdcLongRectangleTorusTranslationIndices L alpha := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangleTorusTranslationOriginIndex_mem L alpha ha

/--
[bdcLongRectangleTorusTranslationOriginIndex_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma bdcLongRectangleTorusTranslationOriginIndex_event_eq
  {L alpha n : ℕ}
-- given
  (ha : 0 < alpha) :
-- imply
  bdcLongRectangleTorusTranslatedEvent L alpha n (bdcLongRectangleTorusTranslationOriginIndex L alpha ha) = bdcLongRectangleBaseEvent alpha n := by
-- proof
  apply StatMech.BeffaraDC.bdcLongRectangleTorusTranslationOriginIndex_event L alpha n ha

/--
[bdcTorusThinCrossingTranslationClosure_iff_pullback_mem_expanded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma bdcTorusThinCrossingTranslationClosure_iff_pullback_mem_expanded_eq
  {L alpha n : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L} :
-- imply
  bdcTorusThinCrossingTranslationClosure L alpha n omega ↔ torusPlanarPullback L omega ∈ bdcLongRectangleTranslationExpandedUnion alpha n := by
-- proof
  apply StatMech.BeffaraDC.bdcTorusThinCrossingTranslationClosure_iff_pullback_mem_expanded L alpha n omega

/--
[bdcTorusThinCrossingTranslationClosure_iff_pullback_mem_finiteExpanded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma bdcTorusThinCrossingTranslationClosure_iff_pullback_mem_finiteExpanded_eq
  {L alpha n : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L} :
-- imply
  bdcTorusThinCrossingTranslationClosure L alpha n omega ↔ torusPlanarPullback L omega ∈ bdcLongRectangleTorusTranslationExpandedUnion L alpha n := by
-- proof
  apply StatMech.BeffaraDC.bdcTorusThinCrossingTranslationClosure_iff_pullback_mem_finiteExpanded L alpha n omega

/--
[thinTranslationClosureCounterexampleConfig_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma thinTranslationClosureCounterexampleConfig_horizontal_eq
  {x y : ZMod 8} :
-- imply
  thinTranslationClosureCounterexampleConfig (torusHorizontalEdge 8 x y) = false := by
-- proof
  apply StatMech.BeffaraDC.thinTranslationClosureCounterexampleConfig_horizontal x y

/--
[thinTranslationClosureCounterexampleConfig_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma thinTranslationClosureCounterexampleConfig_vertical_eq
  {x y : ZMod 8} :
-- imply
  thinTranslationClosureCounterexampleConfig (torusVerticalEdge 8 x y) = decide (x = 0 ∧ (y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4)) := by
-- proof
  apply StatMech.BeffaraDC.thinTranslationClosureCounterexampleConfig_vertical x y

/--
[thinTranslationClosureCounterexample_translated_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma thinTranslationClosureCounterexample_translated_open_eq
  {y : ℤ}
-- given
  (hy0 : 0 ≤ y)
  (hy3 : y ≤ 3) :
-- imply
  IsOpenEdge 2 (torusPlanarPullback 8 (torusAmbientTranslateConfig 8 ![0, 1] thinTranslationClosureCounterexampleConfig)) ![0, y] ![0, y + 1] := by
-- proof
  apply StatMech.BeffaraDC.thinTranslationClosureCounterexample_translated_open y hy0 hy3

/--
[thinTranslationClosureCounterexample_translated_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma thinTranslationClosureCounterexample_translated_crossing_eq :
-- imply
  VerticalCrossing (torusPlanarPullback 8 (torusAmbientTranslateConfig 8 ![0, 1] thinTranslationClosureCounterexampleConfig)) 0 2 0 4 := by
-- proof
  apply StatMech.BeffaraDC.thinTranslationClosureCounterexample_translated_crossing

/--
[thinTranslationClosureCounterexample_mem_closure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma thinTranslationClosureCounterexample_mem_closure_eq :
-- imply
  bdcTorusThinCrossingTranslationClosure 8 2 1 thinTranslationClosureCounterexampleConfig := by
-- proof
  apply StatMech.BeffaraDC.thinTranslationClosureCounterexample_mem_closure

/--
[thinTranslationClosureCounterexample_vertical_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma thinTranslationClosureCounterexample_vertical_iff_eq
  {x y : ℤ} :
-- imply
  torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig s(![x, y], ![x, y + 1]) = true ↔ (x : ZMod 8) = 0 ∧ ((y : ZMod 8) = 1 ∨ (y : ZMod 8) = 2 ∨ (y : ZMod 8) = 3 ∨ (y : ZMod 8) = 4) := by
-- proof
  apply StatMech.BeffaraDC.thinTranslationClosureCounterexample_vertical_iff x y

/--
[thinTranslationClosureCounterexample_cut_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma thinTranslationClosureCounterexample_cut_step_eq
  {a c h : ℤ}
  {p q : Site 2}
-- given
  (hp : p ∈ rect a (a + 2) c (c + 4))
  (hq : q ∈ rect a (a + 2) c (c + 4))
  (hadj : (hypercubicLattice 2).Adj p q)
  (hopen : torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig s(p, q) = true)
  (hple : p 1 ≤ h)
  (hclosed : ∀ x : ℤ, torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig s(![x, h], ![x, h + 1]) ≠ true) :
-- imply
  q 1 ≤ h := by
-- proof
  apply StatMech.BeffaraDC.thinTranslationClosureCounterexample_cut_step hp hq hadj hopen hple hclosed

/--
[thinTranslationClosureCounterexample_cut_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma thinTranslationClosureCounterexample_cut_walk_eq
  {a c h : ℤ}
  {p q : (rect a (a + 2) c (c + 4) : Set (Site 2))}
  {w : (openSubgraphInduce 2 (torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig) (rect a (a + 2) c (c + 4))).Walk p q}
-- given
  (hclosed : ∀ x : ℤ, torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig s(![x, h], ![x, h + 1]) ≠ true)
  (hp : (p : Site 2) 1 ≤ h) :
-- imply
  (q : Site 2) 1 ≤ h := by
-- proof
  apply StatMech.BeffaraDC.thinTranslationClosureCounterexample_cut_walk hclosed w hp

/--
[thinTranslationClosureCounterexample_no_vertical_of_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma thinTranslationClosureCounterexample_no_vertical_of_cut_eq
  {a c h : ℤ}
-- given
  (hch : c ≤ h)
  (hhc : h < c + 4)
  (hclosed : ∀ x : ℤ, torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig s(![x, h], ![x, h + 1]) ≠ true) :
-- imply
  ¬ VerticalCrossing (torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig) a (a + 2) c (c + 4) := by
-- proof
  apply StatMech.BeffaraDC.thinTranslationClosureCounterexample_no_vertical_of_cut hch hhc hclosed

/--
[thinTranslationClosureCounterexample_cut_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma thinTranslationClosureCounterexample_cut_zero_eq
  {x : ℤ} :
-- imply
  torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig s(![x, 0], ![x, 1]) ≠ true := by
-- proof
  apply StatMech.BeffaraDC.thinTranslationClosureCounterexample_cut_zero x

/--
[thinTranslationClosureCounterexample_cut_five](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma thinTranslationClosureCounterexample_cut_five_eq
  {x : ℤ} :
-- imply
  torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig s(![x, 5], ![x, 6]) ≠ true := by
-- proof
  apply StatMech.BeffaraDC.thinTranslationClosureCounterexample_cut_five x

/--
[thinTranslationClosureCounterexample_not_coarse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma thinTranslationClosureCounterexample_not_coarse_eq :
-- imply
  ¬ bdcTorusThinCrossing 8 2 1 thinTranslationClosureCounterexampleConfig := by
-- proof
  apply StatMech.BeffaraDC.thinTranslationClosureCounterexample_not_coarse

/--
[thinTranslationClosureCounterexample_closure_not_coarse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma thinTranslationClosureCounterexample_closure_not_coarse_eq :
-- imply
  bdcTorusThinCrossingTranslationClosure 8 2 1 thinTranslationClosureCounterexampleConfig ∧ ¬ bdcTorusThinCrossing 8 2 1 thinTranslationClosureCounterexampleConfig := by
-- proof
  apply StatMech.BeffaraDC.thinTranslationClosureCounterexample_closure_not_coarse

/--
[not_translationClosure_coarseCover_two_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean)
-/
@[path]
private lemma not_translationClosure_coarseCover_two_one_eq :
-- imply
  ¬ BdcTorusWindingToThinCover 8 2 1 (bdcTorusThinCrossingTranslationClosureEvent 8 2 1) := by
-- proof
  apply StatMech.BeffaraDC.not_translationClosure_coarseCover_two_one


-- created on 2026-10-23
