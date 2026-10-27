import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.rectSideConnectionEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma rectSideConnectionEvent_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {S side : Set V} :
-- imply
  MeasurableSet (E.rectSideConnectionEvent a b c d S side) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectSideConnectionEvent_measurableSet E a b c d S side

/--
[PeriodicPlaneEmbedding.rectSideConnectionEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma rectSideConnectionEvent_isIncreasing_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {S side : Set V} :
-- imply
  IsIncreasing (E.rectSideConnectionEvent a b c d S side) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectSideConnectionEvent_isIncreasing E a b c d S side

/--
[PeriodicPlaneEmbedding.setHitsInfinite_subset_rectSideConnection_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma setHitsInfinite_subset_rectSideConnection_union_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {S : Set V}
-- given
  (hS : S ⊆ E.rectVertices a b c d) :
-- imply
  P.setHitsInfinite S ⊆ E.rectSideConnectionEvent a b c d S (E.rectBottomBoundaryVertices a b c d) ∪ (E.rectSideConnectionEvent a b c d S (E.rectTopBoundaryVertices a b c d) ∪ (E.rectSideConnectionEvent a b c d S (E.rectLeftBoundaryVertices a b c d) ∪ E.rectSideConnectionEvent a b c d S (E.rectRightBoundaryVertices a b c d))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.setHitsInfinite_subset_rectSideConnection_union E a b c d S hS

/--
[PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma rectanglePairMergeErrorUnion_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {L R : Finset V} :
-- imply
  MeasurableSet (E.rectanglePairMergeErrorUnion a b c d L R) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_measurableSet E a b c d L R

/--
[PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_measureReal_mono_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma rectanglePairMergeErrorUnion_measureReal_mono_sources_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {a b c d : Real}
  {L R L' R' : Finset V}
-- given
  (hL : L ⊆ L')
  (hR : R ⊆ R') :
-- imply
  mu.real (E.rectanglePairMergeErrorUnion a b c d L R) ≤ mu.real (E.rectanglePairMergeErrorUnion a b c d L' R') := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_measureReal_mono_sources E mu a b c d hL hR

/--
[PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_subset_pairMergeErrorUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma rectanglePairMergeErrorUnion_subset_pairMergeErrorUnion_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {L R : Finset V}
  {N : Nat}
-- given
  (hbox : (P.orbitBox (P.bufferedRadius N) : Set V) ⊆ E.rectVertices a b c d) :
-- imply
  E.rectanglePairMergeErrorUnion a b c d L R ⊆ P.pairMergeErrorUnion L R N := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_subset_pairMergeErrorUnion E a b c d L R N hbox

/--
[PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_measureReal_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma rectanglePairMergeErrorUnion_measureReal_le_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {a b c d : Real}
  {L R : Finset V}
  {N : Nat}
-- given
  (hbox : (P.orbitBox (P.bufferedRadius N) : Set V) ⊆ E.rectVertices a b c d) :
-- imply
  mu.real (E.rectanglePairMergeErrorUnion a b c d L R) ≤ mu.real (P.pairMergeErrorUnion L R N) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_measureReal_le E mu a b c d L R N hbox

/--
[PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_measureReal_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma rectanglePairMergeErrorUnion_measureReal_tendsto_zero_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : Nat → Real}
  {L R : Finset V}
-- given
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hbox : ∀ N, (P.orbitBox (P.bufferedRadius N) : Set V) ⊆ E.rectVertices (a N) (b N) (c N) (d N)) :
-- imply
  Tendsto (fun N => mu.real (E.rectanglePairMergeErrorUnion (a N) (b N) (c N) (d N) L R)) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_measureReal_tendsto_zero E mu hunique a b c d L R hbox

/--
[PeriodicPlaneEmbedding.configTranslate_preimage_rectanglePairMergeErrorUnion_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma configTranslate_preimage_rectanglePairMergeErrorUnion_subset_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {z : Site 2}
  {a b c d : Real}
  {L R : Finset V}
  {N : Nat}
-- given
  (hbox : (P.shift z '' (P.orbitBox (P.bufferedRadius N) : Set V)) ⊆ E.rectVertices a b c d) :
-- imply
  P.configTranslate z ⁻¹' E.rectanglePairMergeErrorUnion a b c d (L.image (P.shift z)) (R.image (P.shift z)) ⊆ P.pairMergeErrorUnion L R N := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.configTranslate_preimage_rectanglePairMergeErrorUnion_subset E z a b c d L R N hbox

/--
[PeriodicPlaneEmbedding.translated_rectanglePairMergeErrorUnion_measureReal_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma translated_rectanglePairMergeErrorUnion_measureReal_le_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {z : Site 2}
  {a b c d : Real}
  {L R : Finset V}
  {N : Nat}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hbox : (P.shift z '' (P.orbitBox (P.bufferedRadius N) : Set V)) ⊆ E.rectVertices a b c d) :
-- imply
  mu.real (E.rectanglePairMergeErrorUnion a b c d (L.image (P.shift z)) (R.image (P.shift z))) ≤ mu.real (P.pairMergeErrorUnion L R N) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.translated_rectanglePairMergeErrorUnion_measureReal_le E mu hTI z a b c d L R N hbox

/--
[PeriodicPlaneEmbedding.translated_rectanglePairMergeErrorUnion_measureReal_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma translated_rectanglePairMergeErrorUnion_measureReal_tendsto_zero_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {z : Nat → Site 2}
  {a b c d : Nat → Real}
  {L R : Finset V}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hbox : ∀ N, (P.shift (z N) '' (P.orbitBox (P.bufferedRadius N) : Set V)) ⊆ E.rectVertices (a N) (b N) (c N) (d N)) :
-- imply
  Tendsto (fun N => mu.real (E.rectanglePairMergeErrorUnion (a N) (b N) (c N) (d N) (L.image (P.shift (z N))) (R.image (P.shift (z N))))) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.translated_rectanglePairMergeErrorUnion_measureReal_tendsto_zero E mu hTI hunique z a b c d L R hbox

/--
[PeriodicPlaneEmbedding.finiteRectangleJoinedVerticalEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma finiteRectangleJoinedVerticalEvent_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {L R : Finset V} :
-- imply
  MeasurableSet (E.finiteRectangleJoinedVerticalEvent a b c d L R) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteRectangleJoinedVerticalEvent_measurableSet E a b c d L R

/--
[PeriodicPlaneEmbedding.finiteRectangleJoinedVerticalEvent_subset_verticalCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma finiteRectangleJoinedVerticalEvent_subset_verticalCrossing_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {L R : Finset V} :
-- imply
  E.finiteRectangleJoinedVerticalEvent a b c d L R ⊆ E.verticalCrossingEvent a b c d := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteRectangleJoinedVerticalEvent_subset_verticalCrossing E a b c d L R

/--
[PeriodicPlaneEmbedding.finiteRectangleJoinedHorizontalEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma finiteRectangleJoinedHorizontalEvent_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {L R : Finset V} :
-- imply
  MeasurableSet (E.finiteRectangleJoinedHorizontalEvent a b c d L R) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteRectangleJoinedHorizontalEvent_measurableSet E a b c d L R

/--
[PeriodicPlaneEmbedding.finiteRectangleJoinedHorizontalEvent_subset_horizontalCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma finiteRectangleJoinedHorizontalEvent_subset_horizontalCrossing_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {L R : Finset V} :
-- imply
  E.finiteRectangleJoinedHorizontalEvent a b c d L R ⊆ E.horizontalCrossingEvent a b c d := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteRectangleJoinedHorizontalEvent_subset_horizontalCrossing E a b c d L R

/--
[PeriodicPlaneEmbedding.verticalCrossing_measureReal_ge_side_mul_sub_mergeError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma verticalCrossing_measureReal_ge_side_mul_sub_mergeError_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : Real}
  {L R : Finset V}
-- given
  (hFKG : IsFKG mu) :
-- imply
  mu.real (E.rectSideConnectionEvent a b c d (L : Set V) (E.rectBottomBoundaryVertices a b c d)) * mu.real (E.rectSideConnectionEvent a b c d (R : Set V) (E.rectTopBoundaryVertices a b c d)) - mu.real (E.rectanglePairMergeErrorUnion a b c d L R) ≤ mu.real (E.verticalCrossingEvent a b c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.verticalCrossing_measureReal_ge_side_mul_sub_mergeError E mu hFKG a b c d L R

/--
[PeriodicPlaneEmbedding.horizontalCrossing_measureReal_ge_side_mul_sub_mergeError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma horizontalCrossing_measureReal_ge_side_mul_sub_mergeError_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : Real}
  {L R : Finset V}
-- given
  (hFKG : IsFKG mu) :
-- imply
  mu.real (E.rectSideConnectionEvent a b c d (L : Set V) (E.rectLeftBoundaryVertices a b c d)) * mu.real (E.rectSideConnectionEvent a b c d (R : Set V) (E.rectRightBoundaryVertices a b c d)) - mu.real (E.rectanglePairMergeErrorUnion a b c d L R) ≤ mu.real (E.horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.horizontalCrossing_measureReal_ge_side_mul_sub_mergeError E mu hFKG a b c d L R

/--
[PeriodicPlaneEmbedding.setHitsInfinite_inter_rectSide_diff_mergeError_subset_rectSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma setHitsInfinite_inter_rectSide_diff_mergeError_subset_rectSide_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {L R : Finset V}
  {side : Set V} :
-- imply
  (P.setHitsInfinite (R : Set V) ∩ E.rectSideConnectionEvent a b c d (L : Set V) side) \ E.rectanglePairMergeErrorUnion a b c d L R ⊆ E.rectSideConnectionEvent a b c d (R : Set V) side := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.setHitsInfinite_inter_rectSide_diff_mergeError_subset_rectSide E a b c d L R side

/--
[PeriodicPlaneEmbedding.rectSide_measureReal_ge_hits_mul_side_sub_mergeError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma rectSide_measureReal_ge_hits_mul_side_sub_mergeError_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : Real}
  {L R : Finset V}
  {side : Set V}
-- given
  (hFKG : IsFKG mu) :
-- imply
  mu.real (P.setHitsInfinite (R : Set V)) * mu.real (E.rectSideConnectionEvent a b c d (L : Set V) side) - mu.real (E.rectanglePairMergeErrorUnion a b c d L R) ≤ mu.real (E.rectSideConnectionEvent a b c d (R : Set V) side) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectSide_measureReal_ge_hits_mul_side_sub_mergeError E mu hFKG a b c d L R side

/--
[PeriodicPlaneEmbedding.verticalCrossing_ge_preferredSide_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma verticalCrossing_ge_preferredSide_transfer_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : Real}
  {L R : Finset V}
-- given
  (hFKG : IsFKG mu)
  (hOpposite : mu.real (E.rectSideConnectionEvent a b c d (R : Set V) (E.rectBottomBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b c d (R : Set V) (E.rectTopBoundaryVertices a b c d))) :
-- imply
  let A := mu.real (E.rectSideConnectionEvent a b c d (L : Set V) (E.rectBottomBoundaryVertices a b c d)) let H := mu.real (P.setHitsInfinite (R : Set V)) let M := mu.real (E.rectanglePairMergeErrorUnion a b c d L R) A * (H * A - M) - M ≤ mu.real (E.verticalCrossingEvent a b c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.verticalCrossing_ge_preferredSide_transfer E mu hFKG a b c d L R hOpposite

/--
[PeriodicPlaneEmbedding.horizontalCrossing_ge_preferredSide_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma horizontalCrossing_ge_preferredSide_transfer_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : Real}
  {L R : Finset V}
-- given
  (hFKG : IsFKG mu)
  (hOpposite : mu.real (E.rectSideConnectionEvent a b c d (R : Set V) (E.rectLeftBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b c d (R : Set V) (E.rectRightBoundaryVertices a b c d))) :
-- imply
  let A := mu.real (E.rectSideConnectionEvent a b c d (L : Set V) (E.rectLeftBoundaryVertices a b c d)) let H := mu.real (P.setHitsInfinite (R : Set V)) let M := mu.real (E.rectanglePairMergeErrorUnion a b c d L R) A * (H * A - M) - M ≤ mu.real (E.horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.horizontalCrossing_ge_preferredSide_transfer E mu hFKG a b c d L R hOpposite

/--
[dominant_of_four_event_sqrt_trick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma dominant_of_four_event_sqrt_trick_eq
  [DecidableEq V]
  [Countable V]
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {A B C D : Set (ConfigSpace (Sym2 V))}
-- given
  (hFKG : IsFKG mu)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B)
  (hC : IsIncreasing C)
  (hD : IsIncreasing D)
  (hAm : MeasurableSet A)
  (hBm : MeasurableSet B)
  (hCm : MeasurableSet C)
  (hDm : MeasurableSet D)
  (hBA : mu.real B ≤ mu.real A)
  (hCA : mu.real C ≤ mu.real A)
  (hDA : mu.real D ≤ mu.real A) :
-- imply
  1 - Real.sqrt (Real.sqrt (1 - mu.real (A ∪ (B ∪ (C ∪ D))))) ≤ mu.real A := by
-- proof
  apply StatMech.FK.PeriodicPlanar.dominant_of_four_event_sqrt_trick mu hFKG hA hB hC hD hAm hBm hCm hDm hBA hCA hDA

/--
[PeriodicPlaneEmbedding.dominant_bottomSide_measureReal_ge_fourthRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma dominant_bottomSide_measureReal_ge_fourthRoot_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : Real}
  {S : Set V}
-- given
  (hFKG : IsFKG mu)
  (hS : S ⊆ E.rectVertices a b c d)
  (hTop : mu.real (E.rectSideConnectionEvent a b c d S (E.rectTopBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b c d S (E.rectBottomBoundaryVertices a b c d)))
  (hLeft : mu.real (E.rectSideConnectionEvent a b c d S (E.rectLeftBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b c d S (E.rectBottomBoundaryVertices a b c d)))
  (hRight : mu.real (E.rectSideConnectionEvent a b c d S (E.rectRightBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b c d S (E.rectBottomBoundaryVertices a b c d))) :
-- imply
  1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite S))) ≤ mu.real (E.rectSideConnectionEvent a b c d S (E.rectBottomBoundaryVertices a b c d)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.dominant_bottomSide_measureReal_ge_fourthRoot E mu hFKG a b c d S hS hTop hLeft hRight

/--
[PeriodicPlaneEmbedding.dominant_leftSide_measureReal_ge_fourthRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma dominant_leftSide_measureReal_ge_fourthRoot_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : Real}
  {S : Set V}
-- given
  (hFKG : IsFKG mu)
  (hS : S ⊆ E.rectVertices a b c d)
  (hRight : mu.real (E.rectSideConnectionEvent a b c d S (E.rectRightBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b c d S (E.rectLeftBoundaryVertices a b c d)))
  (hBottom : mu.real (E.rectSideConnectionEvent a b c d S (E.rectBottomBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b c d S (E.rectLeftBoundaryVertices a b c d)))
  (hTop : mu.real (E.rectSideConnectionEvent a b c d S (E.rectTopBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b c d S (E.rectLeftBoundaryVertices a b c d))) :
-- imply
  1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite S))) ≤ mu.real (E.rectSideConnectionEvent a b c d S (E.rectLeftBoundaryVertices a b c d)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.dominant_leftSide_measureReal_ge_fourthRoot E mu hFKG a b c d S hS hRight hBottom hTop

/--
[PeriodicPlaneEmbedding.preference_max_bottom_left_ge_fourthRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma preference_max_bottom_left_ge_fourthRoot_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : Real}
  {S : Set V}
-- given
  (hFKG : IsFKG mu)
  (hS : S ⊆ E.rectVertices a b c d)
  (hBottomTop : mu.real (E.rectSideConnectionEvent a b c d S (E.rectTopBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b c d S (E.rectBottomBoundaryVertices a b c d)))
  (hLeftRight : mu.real (E.rectSideConnectionEvent a b c d S (E.rectRightBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b c d S (E.rectLeftBoundaryVertices a b c d))) :
-- imply
  1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite S))) ≤ max (mu.real (E.rectSideConnectionEvent a b c d S (E.rectBottomBoundaryVertices a b c d))) (mu.real (E.rectSideConnectionEvent a b c d S (E.rectLeftBoundaryVertices a b c d))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.preference_max_bottom_left_ge_fourthRoot E mu hFKG a b c d S hS hBottomTop hLeftRight

/--
[PeriodicPlaneEmbedding.dominant_translatedOrbitBox_bottomSide_ge_fourthRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma dominant_translatedOrbitBox_bottomSide_ge_fourthRoot_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {z : Site 2}
  {N : Nat}
  {a b c d : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hbox : (P.shift z '' (P.orbitBox N : Set V)) ⊆ E.rectVertices a b c d)
  (hTop : mu.real (E.rectSideConnectionEvent a b c d (P.shift z '' (P.orbitBox N : Set V)) (E.rectTopBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b c d (P.shift z '' (P.orbitBox N : Set V)) (E.rectBottomBoundaryVertices a b c d)))
  (hLeft : mu.real (E.rectSideConnectionEvent a b c d (P.shift z '' (P.orbitBox N : Set V)) (E.rectLeftBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b c d (P.shift z '' (P.orbitBox N : Set V)) (E.rectBottomBoundaryVertices a b c d)))
  (hRight : mu.real (E.rectSideConnectionEvent a b c d (P.shift z '' (P.orbitBox N : Set V)) (E.rectRightBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b c d (P.shift z '' (P.orbitBox N : Set V)) (E.rectBottomBoundaryVertices a b c d))) :
-- imply
  1 - Real.sqrt (Real.sqrt (1 - mu.real (P.orbitBoxHitsInfinite N))) ≤ mu.real (E.rectSideConnectionEvent a b c d (P.shift z '' (P.orbitBox N : Set V)) (E.rectBottomBoundaryVertices a b c d)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.dominant_translatedOrbitBox_bottomSide_ge_fourthRoot E mu hFKG hTI z N a b c d hbox hTop hLeft hRight

/--
[PeriodicPlaneEmbedding.dominant_translatedOrbitBox_bottomSide_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma dominant_translatedOrbitBox_bottomSide_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {z : Nat → Site 2}
  {a b c d : Nat → Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hexists : mu {omega | P.HasInfiniteCluster omega} = 1)
  (hbox : ∀ N, (P.shift (z N) '' (P.orbitBox N : Set V)) ⊆ E.rectVertices (a N) (b N) (c N) (d N))
  (hTop : ∀ N, mu.real (E.rectSideConnectionEvent (a N) (b N) (c N) (d N) (P.shift (z N) '' (P.orbitBox N : Set V)) (E.rectTopBoundaryVertices (a N) (b N) (c N) (d N))) ≤ mu.real (E.rectSideConnectionEvent (a N) (b N) (c N) (d N) (P.shift (z N) '' (P.orbitBox N : Set V)) (E.rectBottomBoundaryVertices (a N) (b N) (c N) (d N))))
  (hLeft : ∀ N, mu.real (E.rectSideConnectionEvent (a N) (b N) (c N) (d N) (P.shift (z N) '' (P.orbitBox N : Set V)) (E.rectLeftBoundaryVertices (a N) (b N) (c N) (d N))) ≤ mu.real (E.rectSideConnectionEvent (a N) (b N) (c N) (d N) (P.shift (z N) '' (P.orbitBox N : Set V)) (E.rectBottomBoundaryVertices (a N) (b N) (c N) (d N))))
  (hRight : ∀ N, mu.real (E.rectSideConnectionEvent (a N) (b N) (c N) (d N) (P.shift (z N) '' (P.orbitBox N : Set V)) (E.rectRightBoundaryVertices (a N) (b N) (c N) (d N))) ≤ mu.real (E.rectSideConnectionEvent (a N) (b N) (c N) (d N) (P.shift (z N) '' (P.orbitBox N : Set V)) (E.rectBottomBoundaryVertices (a N) (b N) (c N) (d N)))) :
-- imply
  Tendsto (fun N => mu.real (E.rectSideConnectionEvent (a N) (b N) (c N) (d N) (P.shift (z N) '' (P.orbitBox N : Set V)) (E.rectBottomBoundaryVertices (a N) (b N) (c N) (d N)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.dominant_translatedOrbitBox_bottomSide_tendsto_one E mu hFKG hTI hexists z a b c d hbox hTop hLeft hRight

/--
[crossing_tendsto_one_of_preferredSide_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma crossing_tendsto_one_of_preferredSide_transfer_eq
  [DecidableEq V]
  [Countable V]
  {A H M crossing : Nat → Real}
-- given
  (hA : Tendsto A atTop (nhds 1))
  (hH : Tendsto H atTop (nhds 1))
  (hM : Tendsto M atTop (nhds 0))
  (hlower : ∀ N, A N * (H N * A N - M N) - M N ≤ crossing N)
  (hupper : ∀ N, crossing N ≤ 1) :
-- imply
  Tendsto crossing atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.crossing_tendsto_one_of_preferredSide_transfer A H M crossing hA hH hM hlower hupper

/--
[crossing_max_tendsto_one_of_preferredSide_branches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean)
-/
@[path]
private lemma crossing_max_tendsto_one_of_preferredSide_branches_eq
  [DecidableEq V]
  [Countable V]
  {A Hv Hh Mv Mh Cv Ch : Nat → Real}
-- given
  (hA : Tendsto A atTop (nhds 1))
  (hHv : Tendsto Hv atTop (nhds 1))
  (hHh : Tendsto Hh atTop (nhds 1))
  (hMv : Tendsto Mv atTop (nhds 0))
  (hMh : Tendsto Mh atTop (nhds 0))
  (hbranch : ∀ N, A N * (Hv N * A N - Mv N) - Mv N ≤ Cv N ∨ A N * (Hh N * A N - Mh N) - Mh N ≤ Ch N)
  (hCv : ∀ N, Cv N ≤ 1)
  (hCh : ∀ N, Ch N ≤ 1) :
-- imply
  Tendsto (fun N => max (Cv N) (Ch N)) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.crossing_max_tendsto_one_of_preferredSide_branches A Hv Hh Mv Mh Cv Ch hA hHv hHh hMv hMh hbranch hCv hCh


-- created on 2026-10-23
