import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdjacentHeight.Part4
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.axisSwap_bottomBoundaryVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean)
-/
@[path]
private lemma axisSwap_bottomBoundaryVertices_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real} :
-- imply
  E.axisSwap.rectBottomBoundaryVertices a b c d = E.rectLeftBoundaryVertices c d a b := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.axisSwap_bottomBoundaryVertices E a b c d

/--
[PeriodicPlaneEmbedding.axisSwap_topBoundaryVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean)
-/
@[path]
private lemma axisSwap_topBoundaryVertices_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real} :
-- imply
  E.axisSwap.rectTopBoundaryVertices a b c d = E.rectRightBoundaryVertices c d a b := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.axisSwap_topBoundaryVertices E a b c d

/--
[PeriodicPlaneEmbedding.axisSwap_bottomBoundaryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean)
-/
@[path]
private lemma axisSwap_bottomBoundaryEvent_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {S : Set V} :
-- imply
  E.axisSwap.rectSideConnectionEvent a b c d S (E.axisSwap.rectBottomBoundaryVertices a b c d) = E.rectSideConnectionEvent c d a b S (E.rectLeftBoundaryVertices c d a b) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.axisSwap_bottomBoundaryEvent E a b c d S

/--
[PeriodicPlaneEmbedding.axisSwap_topBoundaryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean)
-/
@[path]
private lemma axisSwap_topBoundaryEvent_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {S : Set V} :
-- imply
  E.axisSwap.rectSideConnectionEvent a b c d S (E.axisSwap.rectTopBoundaryVertices a b c d) = E.rectSideConnectionEvent c d a b S (E.rectRightBoundaryVertices c d a b) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.axisSwap_topBoundaryEvent E a b c d S

/--
[PeriodicPlanarDualPair.exists_common_nat_edgeArc_displacement_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean)
-/
@[path]
private lemma exists_common_nat_edgeArc_displacement_bound_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual} :
-- imply
  ∃ B : Nat, 0 < B ∧ (∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ (B : Real)) ∧ (∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ (B : Real)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.exists_common_nat_edgeArc_displacement_bound D

/--
[sheffieldMacroIncrement_gt_eight_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean)
-/
@[path]
private lemma sheffieldMacroIncrement_gt_eight_mul_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {B : Nat} :
-- imply
  (8 : Real) * B < sheffieldMacroIncrement B := by
-- proof
  apply StatMech.FK.PeriodicPlanar.sheffieldMacroIncrement_gt_eight_mul B

/--
[sheffieldMacroArrayCoordinates_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean)
-/
@[path]
private lemma sheffieldMacroArrayCoordinates_adjacent_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {B T : Nat}
  {a0 b0 c0 d0 : Nat → Real}
  {n k : Nat} :
-- imply
  let q := sheffieldMacroArrayCoordinates B T a0 b0 c0 d0 (q n (k + 1)).1 + 4 * B = (q n k).1 ∧ (q n (k + 1)).2.1 - 4 * B = (q n k).2.1 ∧ (q n (k + 1)).2.2.1 = (q n k).2.2.1 + 4 * B ∧ (q n (k + 1)).2.2.2 = (q n k).2.2.2 - 4 * B + (T + 4 * B : Nat) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.sheffieldMacroArrayCoordinates_adjacent B T a0 b0 c0 d0 n k

/--
[sheffieldMacroArrayCoordinates_spans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean)
-/
@[path]
private lemma sheffieldMacroArrayCoordinates_spans_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {B T : Nat}
  {a0 b0 c0 d0 : Nat → Real}
-- given
  (hT : 8 * B < T)
  (hspanX0 : ∀ n, a0 n + 5 * B < b0 n - 5 * B)
  (hspanY0 : ∀ n, c0 n + 5 * B < d0 n - 5 * B) :
-- imply
  let q := sheffieldMacroArrayCoordinates B T a0 b0 c0 d0 (∀ n k, (q n k).1 + 5 * B < (q n k).2.1 - 5 * B) ∧ ∀ n k, (q n k).2.2.1 + 5 * B < (q n k).2.2.2 - 5 * B := by
-- proof
  apply StatMech.FK.PeriodicPlanar.sheffieldMacroArrayCoordinates_spans B T hT a0 b0 c0 d0 hspanX0 hspanY0

/--
[PeriodicPlaneEmbedding.finiteAdjacentHeightJoinedVerticalEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean)
-/
@[path]
private lemma finiteAdjacentHeightJoinedVerticalEvent_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {t : Int}
  {L U : Finset V} :
-- imply
  MeasurableSet (E.finiteAdjacentHeightJoinedVerticalEvent a b c d t L U) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteAdjacentHeightJoinedVerticalEvent_measurableSet E a b c d t L U

/--
[PeriodicPlaneEmbedding.finiteAdjacentHeightJoinedVerticalEvent_subset_verticalCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean)
-/
@[path]
private lemma finiteAdjacentHeightJoinedVerticalEvent_subset_verticalCrossing_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {t : Int}
  {L U : Finset V}
-- given
  (ht : 0 ≤ t) :
-- imply
  E.finiteAdjacentHeightJoinedVerticalEvent a b c d t L U ⊆ E.verticalCrossingEvent a b c (d + t) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteAdjacentHeightJoinedVerticalEvent_subset_verticalCrossing E a b c d t ht L U

/--
[PeriodicPlaneEmbedding.adjacentHeightVerticalCrossing_measureReal_ge_side_mul_sub_mergeError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean)
-/
@[path]
private lemma adjacentHeightVerticalCrossing_measureReal_ge_side_mul_sub_mergeError_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : Real}
  {t : Int}
  {L U : Finset V}
-- given
  (hFKG : IsFKG mu)
  (ht : 0 ≤ t) :
-- imply
  mu.real (E.rectSideConnectionEvent a b c d (L : Set V) (E.rectBottomBoundaryVertices a b c d)) * mu.real (E.rectSideConnectionEvent a b (c + t) (d + t) (U : Set V) (E.rectTopBoundaryVertices a b (c + t) (d + t))) - mu.real (E.rectanglePairMergeErrorUnion a b c (d + t) L U) ≤ mu.real (E.verticalCrossingEvent a b c (d + t)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.adjacentHeightVerticalCrossing_measureReal_ge_side_mul_sub_mergeError E mu hFKG a b c d t ht L U

/--
[PeriodicPlaneEmbedding.adjacentHeightVerticalCrossing_ge_approxPreferredSide_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean)
-/
@[path]
private lemma adjacentHeightVerticalCrossing_ge_approxPreferredSide_transfer_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : Real}
  {t : Int}
  {L R : Finset V}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (ht : 0 ≤ t)
  (hOpposite : mu.real (E.rectSideConnectionEvent a b c d (R : Set V) (E.rectBottomBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b c d (R : Set V) (E.rectTopBoundaryVertices a b c d)) + epsilon) :
-- imply
  let U := R.image (P.shift (verticalShift t)) let A := mu.real (E.rectSideConnectionEvent a b c d (L : Set V) (E.rectBottomBoundaryVertices a b c d)) let H := mu.real (P.setHitsInfinite (R : Set V)) let Mtransfer := mu.real (E.rectanglePairMergeErrorUnion a b c d L R) let Mjoin := mu.real (E.rectanglePairMergeErrorUnion a b c (d + t) L U) A * (H * A - Mtransfer - epsilon) - Mjoin ≤ mu.real (E.verticalCrossingEvent a b c (d + t)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.adjacentHeightVerticalCrossing_ge_approxPreferredSide_transfer E mu hFKG hTI a b c d t ht L R epsilon hOpposite

/--
[PeriodicPlaneEmbedding.outwardVerticalCrossing_ge_approxPreferredSide_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean)
-/
@[path]
private lemma outwardVerticalCrossing_ge_approxPreferredSide_transfer_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : Real}
  {pad : Int}
  {L R : Finset V}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hpad : 0 ≤ pad)
  (hOpposite : mu.real (E.rectSideConnectionEvent a b c d (R : Set V) (E.rectBottomBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b c d (R : Set V) (E.rectTopBoundaryVertices a b c d)) + epsilon) :
-- imply
  let Ldown := L.image (P.shift (verticalShift (-pad))) let Rdown := R.image (P.shift (verticalShift (-pad))) let Rup := R.image (P.shift (verticalShift pad)) let A := mu.real (E.rectSideConnectionEvent a b c d (L : Set V) (E.rectBottomBoundaryVertices a b c d)) let H := mu.real (P.setHitsInfinite (R : Set V)) let Mtransfer := mu.real (E.rectanglePairMergeErrorUnion a b (c - pad) (d - pad) Ldown Rdown) let Mjoin := mu.real (E.rectanglePairMergeErrorUnion a b (c - pad) (d + pad) Ldown Rup) A * (H * A - Mtransfer - epsilon) - Mjoin ≤ mu.real (E.verticalCrossingEvent a b (c - pad) (d + pad)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.outwardVerticalCrossing_ge_approxPreferredSide_transfer E mu hFKG hTI a b c d pad hpad L R epsilon hOpposite

/--
[PeriodicPlaneEmbedding.outwardHorizontalCrossing_ge_approxPreferredSide_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean)
-/
@[path]
private lemma outwardHorizontalCrossing_ge_approxPreferredSide_transfer_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : Real}
  {pad : Int}
  {L R : Finset V}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hpad : 0 ≤ pad)
  (hOpposite : mu.real (E.rectSideConnectionEvent a b c d (R : Set V) (E.rectLeftBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b c d (R : Set V) (E.rectRightBoundaryVertices a b c d)) + epsilon) :
-- imply
  let Lleft := L.image (P.shift (horizontalShift (-pad))) let Rleft := R.image (P.shift (horizontalShift (-pad))) let Rright := R.image (P.shift (horizontalShift pad)) let A := mu.real (E.rectSideConnectionEvent a b c d (L : Set V) (E.rectLeftBoundaryVertices a b c d)) let H := mu.real (P.setHitsInfinite (R : Set V)) let Mtransfer := mu.real (E.rectanglePairMergeErrorUnion (a - pad) (b - pad) c d Lleft Rleft) let Mjoin := mu.real (E.rectanglePairMergeErrorUnion (a - pad) (b + pad) c d Lleft Rright) A * (H * A - Mtransfer - epsilon) - Mjoin ≤ mu.real (E.horizontalCrossingEvent (a - pad) (b + pad) c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.outwardHorizontalCrossing_ge_approxPreferredSide_transfer E mu hFKG hTI a b c d pad hpad L R epsilon hOpposite

/--
[PeriodicPlaneEmbedding.exists_outward_approxPreferredSide_crossing_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean)
-/
@[path]
private lemma exists_outward_approxPreferredSide_crossing_branch_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : Real}
  {pad : Int}
  {width height : Nat}
  {epsilon : Real}
  {source : PreferenceGridVertex width height → Finset V}
  {bottom top left right : PreferenceGridVertex width height → Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hpad : 0 ≤ pad)
  (hwidth : 0 < width)
  (hheight : 0 < height)
  (hepsilon : 0 ≤ epsilon)
  (hsource : ∀ x, (source x : Set V) ⊆ E.rectVertices a b c d)
  (hbottomScore : ∀ x, bottom x = mu.real (E.rectSideConnectionEvent a b c d (source x : Set V) (E.rectBottomBoundaryVertices a b c d)))
  (htopScore : ∀ x, top x = mu.real (E.rectSideConnectionEvent a b c d (source x : Set V) (E.rectTopBoundaryVertices a b c d)))
  (hleftScore : ∀ x, left x = mu.real (E.rectSideConnectionEvent a b c d (source x : Set V) (E.rectLeftBoundaryVertices a b c d)))
  (hrightScore : ∀ x, right x = mu.real (E.rectSideConnectionEvent a b c d (source x : Set V) (E.rectRightBoundaryVertices a b c d)))
  (hbottom : ∀ i : Fin (width + 1), top (i, 0) ≤ bottom (i, 0) + epsilon)
  (htop : ∀ i : Fin (width + 1), bottom (i, Fin.last height) ≤ top (i, Fin.last height) + epsilon)
  (hleft : ∀ j : Fin (height + 1), right (0, j) ≤ left (0, j) + epsilon)
  (hright : ∀ j : Fin (height + 1), left (Fin.last width, j) ≤ right (Fin.last width, j) + epsilon) :
-- imply
  ∃ x xVertical xHorizontal : PreferenceGridVertex width height, KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) ∧ KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) ∧ ((1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤ bottom x + epsilon ∧ let Ldown := (source x).image (P.shift (verticalShift (-pad))) let Rdown := (source xVertical).image (P.shift (verticalShift (-pad))) let Rup := (source xVertical).image (P.shift (verticalShift pad)) let Mtransfer := mu.real (E.rectanglePairMergeErrorUnion a b (c - pad) (d - pad) Ldown Rdown) let Mjoin := mu.real (E.rectanglePairMergeErrorUnion a b (c - pad) (d + pad) Ldown Rup) bottom x * (mu.real (P.setHitsInfinite (source xVertical : Set V)) * bottom x - Mtransfer - epsilon) - Mjoin ≤ mu.real (E.verticalCrossingEvent a b (c - pad) (d + pad))) ∨ (1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤ left x + epsilon ∧ let Lleft := (source x).image (P.shift (horizontalShift (-pad))) let Rleft := (source xHorizontal).image (P.shift (horizontalShift (-pad))) let Rright := (source xHorizontal).image (P.shift (horizontalShift pad)) let Mtransfer := mu.real (E.rectanglePairMergeErrorUnion (a - pad) (b - pad) c d Lleft Rleft) let Mjoin := mu.real (E.rectanglePairMergeErrorUnion (a - pad) (b + pad) c d Lleft Rright) left x * (mu.real (P.setHitsInfinite (source xHorizontal : Set V)) * left x - Mtransfer - epsilon) - Mjoin ≤ mu.real (E.horizontalCrossingEvent (a - pad) (b + pad) c d))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_outward_approxPreferredSide_crossing_branch E mu hFKG hTI a b c d pad hpad hwidth hheight epsilon hepsilon source bottom top left right hsource hbottomScore htopScore hleftScore hrightScore hbottom htop hleft hright

/--
[PeriodicPlaneEmbedding.exists_uniformTemplate_outwardPreference_crossing_max_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean)
-/
@[path]
private lemma exists_uniformTemplate_outwardPreference_crossing_max_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {template : Nat → Finset V}
  {pad : Nat → Int}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (htemplateHit : Tendsto (fun n => mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
  (hpad : ∀ n, 0 ≤ pad n) :
-- imply
  ∃ radius : Nat → Nat, ∀ (width height : Nat → Nat) (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n) (base : Nat → Site 2) (a b c d epsilon : Nat → Real) (bottom top left right : (n : Nat) → PreferenceGridVertex (width n) (height n) → Real), Tendsto epsilon atTop (nhds 0) → (∀ n, 0 ≤ epsilon n) → (∀ n (v : PreferenceGridVertex (width n) (height n)), ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) ⊆ E.rectVertices (a n) (b n) (c n) (d n)) → (∀ n (v : PreferenceGridVertex (width n) (height n)), (P.shift (base n + preferenceGridSite v + verticalShift (-(pad n))) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a n) (b n) (c n - pad n) (d n - pad n)) → (∀ n (v : PreferenceGridVertex (width n) (height n)), (P.shift (base n + preferenceGridSite v + verticalShift (-(pad n))) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a n) (b n) (c n - pad n) (d n + pad n)) → (∀ n (v : PreferenceGridVertex (width n) (height n)), (P.shift (base n + preferenceGridSite v + horizontalShift (-(pad n))) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a n - pad n) (b n - pad n) (c n) (d n)) → (∀ n (v : PreferenceGridVertex (width n) (height n)), (P.shift (base n + preferenceGridSite v + horizontalShift (-(pad n))) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a n - pad n) (b n + pad n) (c n) (d n)) → (∀ n v, bottom n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n v, top n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n v, left n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n v, right n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n i, top n (i, 0) ≤ bottom n (i, 0) + epsilon n) → (∀ n i, bottom n (i, Fin.last (height n)) ≤ top n (i, Fin.last (height n)) + epsilon n) → (∀ n j, right n (0, j) ≤ left n (0, j) + epsilon n) → (∀ n j, left n (Fin.last (width n), j) ≤ right n (Fin.last (width n), j) + epsilon n) → Tendsto (fun n => max (mu.real (E.verticalCrossingEvent (a n) (b n) (c n - pad n) (d n + pad n))) (mu.real (E.horizontalCrossingEvent (a n - pad n) (b n + pad n) (c n) (d n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformTemplate_outwardPreference_crossing_max_tendsto_one E mu hFKG hTI hunique template htemplateHit pad hpad

/--
[PeriodicPlaneEmbedding.exists_uniformTemplate_outwardBoundaryScores_crossing_max_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean)
-/
@[path]
private lemma exists_uniformTemplate_outwardBoundaryScores_crossing_max_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {template : Nat → Finset V}
  {pad : Nat → Int}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (htemplateHit : Tendsto (fun n ↦ mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
  (hpad : ∀ n, 0 ≤ pad n) :
-- imply
  ∃ radius : Nat → Nat, ∀ (width height : Nat → Nat) (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n) (base : Nat → Site 2) (a b c d p : Nat → Real), Tendsto p atTop (nhds 1) → (∀ n, p n ≤ 1) → (∀ n (v : PreferenceGridVertex (width n) (height n)), ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) ⊆ E.rectVertices (a n) (b n) (c n) (d n)) → (∀ n (v : PreferenceGridVertex (width n) (height n)), (P.shift (base n + preferenceGridSite v + verticalShift (-(pad n))) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a n) (b n) (c n - pad n) (d n - pad n)) → (∀ n (v : PreferenceGridVertex (width n) (height n)), (P.shift (base n + preferenceGridSite v + verticalShift (-(pad n))) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a n) (b n) (c n - pad n) (d n + pad n)) → (∀ n (v : PreferenceGridVertex (width n) (height n)), (P.shift (base n + preferenceGridSite v + horizontalShift (-(pad n))) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a n - pad n) (b n - pad n) (c n) (d n)) → (∀ n (v : PreferenceGridVertex (width n) (height n)), (P.shift (base n + preferenceGridSite v + horizontalShift (-(pad n))) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a n - pad n) (b n + pad n) (c n) (d n)) → (∀ n (i : Fin (width n + 1)), p n ≤ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite (i, (0 : Fin (height n + 1))))) : Set V) (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n (i : Fin (width n + 1)), p n ≤ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite (i, Fin.last (height n)))) : Set V) (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n (j : Fin (height n + 1)), p n ≤ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite ((0 : Fin (width n + 1)), j))) : Set V) (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n (j : Fin (height n + 1)), p n ≤ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite (Fin.last (width n), j))) : Set V) (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) → Tendsto (fun n ↦ max (mu.real (E.verticalCrossingEvent (a n) (b n) (c n - pad n) (d n + pad n))) (mu.real (E.horizontalCrossingEvent (a n - pad n) (b n + pad n) (c n) (d n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformTemplate_outwardBoundaryScores_crossing_max_tendsto_one E mu hFKG hTI hunique template htemplateHit pad hpad

/--
[PeriodicPlaneEmbedding.exists_adjacentHeight_approxPreferredSide_crossing_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean)
-/
@[path]
private lemma exists_adjacentHeight_approxPreferredSide_crossing_branch_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : Real}
  {t : Int}
  {width height : Nat}
  {epsilon : Real}
  {source : PreferenceGridVertex width height → Finset V}
  {bottom top left right : PreferenceGridVertex width height → Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (ht : 0 ≤ t)
  (hwidth : 0 < width)
  (hheight : 0 < height)
  (hepsilon : 0 ≤ epsilon)
  (hsource : ∀ x, (source x : Set V) ⊆ E.rectVertices a b c d)
  (hbottomScore : ∀ x, bottom x = mu.real (E.rectSideConnectionEvent a b c d (source x : Set V) (E.rectBottomBoundaryVertices a b c d)))
  (htopScore : ∀ x, top x = mu.real (E.rectSideConnectionEvent a b c d (source x : Set V) (E.rectTopBoundaryVertices a b c d)))
  (hleftScore : ∀ x, left x = mu.real (E.rectSideConnectionEvent a b c d (source x : Set V) (E.rectLeftBoundaryVertices a b c d)))
  (hrightScore : ∀ x, right x = mu.real (E.rectSideConnectionEvent a b c d (source x : Set V) (E.rectRightBoundaryVertices a b c d)))
  (hbottom : ∀ i : Fin (width + 1), top (i, 0) ≤ bottom (i, 0) + epsilon)
  (htop : ∀ i : Fin (width + 1), bottom (i, Fin.last height) ≤ top (i, Fin.last height) + epsilon)
  (hleft : ∀ j : Fin (height + 1), right (0, j) ≤ left (0, j) + epsilon)
  (hright : ∀ j : Fin (height + 1), left (Fin.last width, j) ≤ right (Fin.last width, j) + epsilon) :
-- imply
  ∃ x xVertical xHorizontal : PreferenceGridVertex width height, KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) ∧ KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) ∧ ((1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤ bottom x + epsilon ∧ let U := (source xVertical).image (P.shift (verticalShift t)) let Mtransfer := mu.real (E.rectanglePairMergeErrorUnion a b c d (source x) (source xVertical)) let Mjoin := mu.real (E.rectanglePairMergeErrorUnion a b c (d + t) (source x) U) bottom x * (mu.real (P.setHitsInfinite (source xVertical : Set V)) * bottom x - Mtransfer - epsilon) - Mjoin ≤ mu.real (E.verticalCrossingEvent a b c (d + t))) ∨ (1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤ left x + epsilon ∧ left x * (mu.real (P.setHitsInfinite (source xHorizontal : Set V)) * left x - mu.real (E.rectanglePairMergeErrorUnion a b c d (source x) (source xHorizontal)) - epsilon) - mu.real (E.rectanglePairMergeErrorUnion a b c d (source x) (source xHorizontal)) ≤ mu.real (E.horizontalCrossingEvent a b c d))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_adjacentHeight_approxPreferredSide_crossing_branch E mu hFKG hTI a b c d t ht hwidth hheight epsilon hepsilon source bottom top left right hsource hbottomScore htopScore hleftScore hrightScore hbottom htop hleft hright

/--
[PeriodicPlaneEmbedding.exists_uniformTemplate_adjacentHeightPreference_crossing_max_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean)
-/
@[path]
private lemma exists_uniformTemplate_adjacentHeightPreference_crossing_max_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {template : Nat → Finset V}
  {step : Nat → Int}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (htemplateHit : Tendsto (fun n => mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
  (hstep : ∀ n, 0 ≤ step n) :
-- imply
  ∃ radius : Nat → Nat, ∀ (width height : Nat → Nat) (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n) (base : Nat → Site 2) (a b c d epsilon : Nat → Real) (bottom top left right : (n : Nat) → PreferenceGridVertex (width n) (height n) → Real), Tendsto epsilon atTop (nhds 0) → (∀ n, 0 ≤ epsilon n) → (∀ n (v : PreferenceGridVertex (width n) (height n)), ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) ⊆ E.rectVertices (a n) (b n) (c n) (d n)) → (∀ n (v : PreferenceGridVertex (width n) (height n)), (P.shift (base n + preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a n) (b n) (c n) (d n)) → (∀ n v, bottom n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n v, top n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n v, left n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n v, right n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n i, top n (i, 0) ≤ bottom n (i, 0) + epsilon n) → (∀ n i, bottom n (i, Fin.last (height n)) ≤ top n (i, Fin.last (height n)) + epsilon n) → (∀ n j, right n (0, j) ≤ left n (0, j) + epsilon n) → (∀ n j, left n (Fin.last (width n), j) ≤ right n (Fin.last (width n), j) + epsilon n) → Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))) (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n + step n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformTemplate_adjacentHeightPreference_crossing_max_tendsto_one E mu hFKG hTI hunique template htemplateHit step hstep

/--
[PeriodicPlaneEmbedding.exists_uniformTemplate_adjacentHeightBoundaryScores_crossing_max_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean)
-/
@[path]
private lemma exists_uniformTemplate_adjacentHeightBoundaryScores_crossing_max_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {template : Nat → Finset V}
  {step : Nat → Int}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (htemplateHit : Tendsto (fun n => mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
  (hstep : ∀ n, 0 ≤ step n) :
-- imply
  ∃ radius : Nat → Nat, ∀ (width height : Nat → Nat) (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n) (base : Nat → Site 2) (a b c d p : Nat → Real), Tendsto p atTop (nhds 1) → (∀ n, p n ≤ 1) → (∀ n (v : PreferenceGridVertex (width n) (height n)), ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) ⊆ E.rectVertices (a n) (b n) (c n) (d n)) → (∀ n (v : PreferenceGridVertex (width n) (height n)), (P.shift (base n + preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a n) (b n) (c n) (d n)) → (∀ n (i : Fin (width n + 1)), p n ≤ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite (i, (0 : Fin (height n + 1))))) : Set V) (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n (i : Fin (width n + 1)), p n ≤ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite (i, Fin.last (height n)))) : Set V) (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n (j : Fin (height n + 1)), p n ≤ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite ((0 : Fin (width n + 1)), j))) : Set V) (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n (j : Fin (height n + 1)), p n ≤ mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite (Fin.last (width n), j))) : Set V) (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) → Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))) (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n + step n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformTemplate_adjacentHeightBoundaryScores_crossing_max_tendsto_one E mu hFKG hTI hunique template htemplateHit step hstep

/--
[PeriodicPlanarDualPair.macroArray_contradiction_of_crossing_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdjacentHeight.lean)
-/
@[path]
private lemma macroArray_contradiction_of_crossing_limits_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B T : Nat}
  {a0 b0 c0 d0 : Nat → Real}
  {K : Nat → Nat}
-- given
  (hBpos : 0 < B)
  (hT : 8 * B < T)
  (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ (B : Real))
  (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ (B : Real))
  (hspanX0 : ∀ n, a0 n + 5 * B < b0 n - 5 * B)
  (hspanY0 : ∀ n, c0 n + 5 * B < d0 n - 5 * B)
  (hverticalStart : Tendsto (fun n => mu.real (D.primalEmbedding.verticalCrossingEvent (a0 n + 4 * B) (b0 n - 4 * B) (c0 n) (d0 n))) atTop (nhds 1))
  (hhorizontalEnd : let q := sheffieldMacroArrayCoordinates B T a0 b0 c0 d0 Tendsto (fun n => mu.real (D.primalEmbedding.horizontalCrossingEvent (q n (K n + 1)).1 (q n (K n + 1)).2.1 ((q n (K n + 1)).2.2.1 + 4 * B) ((q n (K n + 1)).2.2.2 - 4 * B))) atTop (nhds 1))
  (hprimalAdjacent : let q := sheffieldMacroArrayCoordinates B T a0 b0 c0 d0 ∀ k : Nat → Nat, (∀ n, k n < K n + 1) → Tendsto (fun n => max (mu.real (D.primalEmbedding.horizontalCrossingEvent (q n (k n)).1 (q n (k n)).2.1 ((q n (k n)).2.2.1 + 4 * B) ((q n (k n)).2.2.2 - 4 * B))) (mu.real (D.primalEmbedding.verticalCrossingEvent (q n (k n)).1 (q n (k n)).2.1 ((q n (k n)).2.2.1 + 4 * B) ((q n (k n)).2.2.2 - 4 * B + (T + 4 * B : Nat))))) atTop (nhds 1))
  (hdual : let q := sheffieldMacroArrayCoordinates B T a0 b0 c0 d0 ∀ k : Nat → Nat, Tendsto (fun n => max (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent ((q n (k n)).1 + 4 * B) ((q n (k n)).2.1 - 4 * B) ((q n (k n)).2.2.1) ((q n (k n)).2.2.2))) (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent ((q n (k n)).1) ((q n (k n)).2.1) ((q n (k n)).2.2.1 + 4 * B) ((q n (k n)).2.2.2 - 4 * B)))) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.macroArray_contradiction_of_crossing_limits D mu B T hBpos hT hBp hBd a0 b0 c0 d0 K hspanX0 hspanY0 hverticalStart hhorizontalEnd hprimalAdjacent hdual


-- created on 2026-10-23
