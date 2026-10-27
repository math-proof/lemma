import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryGrid
open Filter MeasureTheory Set Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.shift_image_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryGrid.lean)
-/
@[path]
private lemma shift_image_shift_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z w : Site 2}
  {S : Set V} :
-- imply
  P.shift w '' (P.shift z '' S) = P.shift (z + w) '' S := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.shift_image_shift P z w S

/--
[exists_cofinalIndex_weightedFourDefects_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryGrid.lean)
-/
@[path]
private lemma exists_cofinalIndex_weightedFourDefects_tendsto_zero_eq
  [DecidableEq V]
  [Countable V]
  {fBottom fTop fLeft fRight : Nat → Real}
-- given
  (hfBottom : Tendsto fBottom atTop (nhds 1))
  (hfTop : Tendsto fTop atTop (nhds 1))
  (hfLeft : Tendsto fLeft atTop (nhds 1))
  (hfRight : Tendsto fRight atTop (nhds 1))
  (hfBottomLe : ∀ n, fBottom n ≤ 1)
  (hfTopLe : ∀ n, fTop n ≤ 1)
  (hfLeftLe : ∀ n, fLeft n ≤ 1)
  (hfRightLe : ∀ n, fRight n ≤ 1)
  (width height : Nat → Nat) :
-- imply
  ∃ index : Nat → Nat, (∀ n, n ≤ index n) ∧ Tendsto (fun n => (width n + 1 : Real) * (1 - fBottom (index n)) + (width n + 1 : Real) * (1 - fTop (index n)) + (height n + 1 : Real) * (1 - fLeft (index n)) + (height n + 1 : Real) * (1 - fRight (index n))) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_cofinalIndex_weightedFourDefects_tendsto_zero fBottom fTop fLeft fRight hfBottom hfTop hfLeft hfRight hfBottomLe hfTopLe hfLeftLe hfRightLe width height

/--
[exists_cofinalIndex_finsetSum_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryGrid.lean)
-/
@[path]
private lemma exists_cofinalIndex_finsetSum_tendsto_zero_eq
  [DecidableEq V]
  [Countable V]
  {f : Nat → Nat → Real}
-- given
  (hf : ∀ k, Tendsto (f k) atTop (nhds 0)) :
-- imply
  ∃ index : Nat → Nat, (∀ n, n ≤ index n) ∧ Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), f k (index n)) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_cofinalIndex_finsetSum_tendsto_zero f hf

/--
[rectangleEndpointPreferenceError_le_boundaryDefects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryGrid.lean)
-/
@[path]
private lemma rectangleEndpointPreferenceError_le_boundaryDefects_eq
  [DecidableEq V]
  [Countable V]
  {n m : Nat}
  {bottom top left right : PreferenceGridVertex n m → Real}
  {deltaBottom deltaTop deltaLeft deltaRight : Real}
-- given
  (hdeltaBottom : 0 ≤ deltaBottom)
  (hdeltaTop : 0 ≤ deltaTop)
  (hdeltaLeft : 0 ≤ deltaLeft)
  (hdeltaRight : 0 ≤ deltaRight)
  (hbottom : ∀ i : Fin (n + 1), 1 - deltaBottom ≤ bottom (i, 0))
  (htop : ∀ i : Fin (n + 1), 1 - deltaTop ≤ top (i, Fin.last m))
  (hleft : ∀ j : Fin (m + 1), 1 - deltaLeft ≤ left (0, j))
  (hright : ∀ j : Fin (m + 1), 1 - deltaRight ≤ right (Fin.last n, j))
  (hbottomLe : ∀ x, bottom x ≤ 1)
  (htopLe : ∀ x, top x ≤ 1)
  (hleftLe : ∀ x, left x ≤ 1)
  (hrightLe : ∀ x, right x ≤ 1) :
-- imply
  rectangleEndpointPreferenceError bottom top left right ≤ (n + 1 : Real) * deltaBottom + (n + 1 : Real) * deltaTop + (m + 1 : Real) * deltaLeft + (m + 1 : Real) * deltaRight := by
-- proof
  apply StatMech.FK.PeriodicPlanar.rectangleEndpointPreferenceError_le_boundaryDefects bottom top left right deltaBottom deltaTop deltaLeft deltaRight hdeltaBottom hdeltaTop hdeltaLeft hdeltaRight hbottom htop hleft hright hbottomLe htopLe hleftLe hrightLe

/--
[rectangleEndpointPreferenceError_le_boundaryProbabilities](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryGrid.lean)
-/
@[path]
private lemma rectangleEndpointPreferenceError_le_boundaryProbabilities_eq
  [DecidableEq V]
  [Countable V]
  {n m : Nat}
  {bottom top left right : PreferenceGridVertex n m → Real}
  {pBottom pTop pLeft pRight : Real}
-- given
  (hpBottom : pBottom ≤ 1)
  (hpTop : pTop ≤ 1)
  (hpLeft : pLeft ≤ 1)
  (hpRight : pRight ≤ 1)
  (hbottom : ∀ i : Fin (n + 1), pBottom ≤ bottom (i, 0))
  (htop : ∀ i : Fin (n + 1), pTop ≤ top (i, Fin.last m))
  (hleft : ∀ j : Fin (m + 1), pLeft ≤ left (0, j))
  (hright : ∀ j : Fin (m + 1), pRight ≤ right (Fin.last n, j))
  (hbottomLe : ∀ x, bottom x ≤ 1)
  (htopLe : ∀ x, top x ≤ 1)
  (hleftLe : ∀ x, left x ≤ 1)
  (hrightLe : ∀ x, right x ≤ 1) :
-- imply
  rectangleEndpointPreferenceError bottom top left right ≤ (n + 1 : Real) * (1 - pBottom) + (n + 1 : Real) * (1 - pTop) + (m + 1 : Real) * (1 - pLeft) + (m + 1 : Real) * (1 - pRight) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.rectangleEndpointPreferenceError_le_boundaryProbabilities bottom top left right pBottom pTop pLeft pRight hpBottom hpTop hpLeft hpRight hbottom htop hleft hright hbottomLe htopLe hleftLe hrightLe

/--
[rectangleEndpointPreferenceError_tendsto_zero_of_boundaryProbabilities](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryGrid.lean)
-/
@[path]
private lemma rectangleEndpointPreferenceError_tendsto_zero_of_boundaryProbabilities_eq
  [DecidableEq V]
  [Countable V]
  {bottom top left right : (n : Nat) → PreferenceGridVertex (width n) (height n) → Real}
  {pBottom pTop pLeft pRight : Nat → Real}
-- given
  (width height : Nat → Nat)
  (hpBottom : ∀ n, pBottom n ≤ 1)
  (hpTop : ∀ n, pTop n ≤ 1)
  (hpLeft : ∀ n, pLeft n ≤ 1)
  (hpRight : ∀ n, pRight n ≤ 1)
  (hbottom : ∀ n (i : Fin (width n + 1)), pBottom n ≤ bottom n (i, 0))
  (htop : ∀ n (i : Fin (width n + 1)), pTop n ≤ top n (i, Fin.last (height n)))
  (hleft : ∀ n (j : Fin (height n + 1)), pLeft n ≤ left n (0, j))
  (hright : ∀ n (j : Fin (height n + 1)), pRight n ≤ right n (Fin.last (width n), j))
  (hbottomLe : ∀ n x, bottom n x ≤ 1)
  (htopLe : ∀ n x, top n x ≤ 1)
  (hleftLe : ∀ n x, left n x ≤ 1)
  (hrightLe : ∀ n x, right n x ≤ 1)
  (hdefects : Tendsto (fun n => (width n + 1 : Real) * (1 - pBottom n) + (width n + 1 : Real) * (1 - pTop n) + (height n + 1 : Real) * (1 - pLeft n) + (height n + 1 : Real) * (1 - pRight n)) atTop (nhds 0)) :
-- imply
  Tendsto (fun n => rectangleEndpointPreferenceError (bottom n) (top n) (left n) (right n)) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.rectangleEndpointPreferenceError_tendsto_zero_of_boundaryProbabilities width height bottom top left right pBottom pTop pLeft pRight hpBottom hpTop hpLeft hpRight hbottom htop hleft hright hbottomLe htopLe hleftLe hrightLe hdefects

/--
[PeriodicPlaneEmbedding.preferenceGrid_translatedSet_subset_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryGrid.lean)
-/
@[path]
private lemma preferenceGrid_translatedSet_subset_rect_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {n m : Nat}
  {base : Site 2}
  {S : Set V}
  {a b c d a' b' c' d' : Real}
-- given
  (hbase : P.shift base '' S ⊆ E.rectVertices a b c d)
  (ha : a' ≤ a)
  (hb : b + n ≤ b')
  (hc : c' ≤ c)
  (hd : d + m ≤ d') :
-- imply
  ∀ v : PreferenceGridVertex n m, P.shift (base + preferenceGridSite v) '' S ⊆ E.rectVertices a' b' c' d' := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.preferenceGrid_translatedSet_subset_rect E base S hbase ha hb hc hd

/--
[PeriodicPlaneEmbedding.exists_uniformTemplate_intrinsicError_crossing_max_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryGrid.lean)
-/
@[path]
private lemma exists_uniformTemplate_intrinsicError_crossing_max_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {template : Nat → Finset V}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (htemplateHit : Tendsto (fun n => mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1)) :
-- imply
  ∃ radius : Nat → Nat, ∀ (width height : Nat → Nat) (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n) (base : Nat → Site 2) (a b c d : Nat → Real) (bottom top left right : (n : Nat) → PreferenceGridVertex (width n) (height n) → Real), (∀ n (v : PreferenceGridVertex (width n) (height n)), ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) ⊆ E.rectVertices (a n) (b n) (c n) (d n)) → (∀ n (v : PreferenceGridVertex (width n) (height n)), (P.shift (base n + preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a n) (b n) (c n) (d n)) → (∀ n v, bottom n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n v, top n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n v, left n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n v, right n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) → Tendsto (fun n => rectangleEndpointPreferenceError (bottom n) (top n) (left n) (right n)) atTop (nhds 0) → Tendsto (fun n => max (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n))) (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformTemplate_intrinsicError_crossing_max_tendsto_one E mu hFKG hTI hunique template htemplateHit

/--
[PeriodicPlaneEmbedding.exists_uniformTemplate_boundaryScores_crossing_max_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryGrid.lean)
-/
@[path]
private lemma exists_uniformTemplate_boundaryScores_crossing_max_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {template : Nat → Finset V}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (htemplateHit : Tendsto (fun n => mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1)) :
-- imply
  ∃ radius : Nat → Nat, ∀ (width height : Nat → Nat) (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n) (base : Nat → Site 2) (a b c d : Nat → Real) (bottom top left right : (n : Nat) → PreferenceGridVertex (width n) (height n) → Real) (pBottom pTop pLeft pRight : Nat → Real), (∀ n (v : PreferenceGridVertex (width n) (height n)), ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) ⊆ E.rectVertices (a n) (b n) (c n) (d n)) → (∀ n (v : PreferenceGridVertex (width n) (height n)), (P.shift (base n + preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a n) (b n) (c n) (d n)) → (∀ n v, bottom n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n v, top n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n v, left n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n v, right n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n, pBottom n ≤ 1) → (∀ n, pTop n ≤ 1) → (∀ n, pLeft n ≤ 1) → (∀ n, pRight n ≤ 1) → (∀ n (i : Fin (width n + 1)), pBottom n ≤ bottom n (i, 0)) → (∀ n (i : Fin (width n + 1)), pTop n ≤ top n (i, Fin.last (height n))) → (∀ n (j : Fin (height n + 1)), pLeft n ≤ left n (0, j)) → (∀ n (j : Fin (height n + 1)), pRight n ≤ right n (Fin.last (width n), j)) → Tendsto (fun n => (width n + 1 : Real) * (1 - pBottom n) + (width n + 1 : Real) * (1 - pTop n) + (height n + 1 : Real) * (1 - pLeft n) + (height n + 1 : Real) * (1 - pRight n)) atTop (nhds 0) → Tendsto (fun n => max (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n))) (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformTemplate_boundaryScores_crossing_max_tendsto_one E mu hFKG hTI hunique template htemplateHit

/--
[PeriodicPlaneEmbedding.rectLeftConnection_tangential_measureReal_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryGrid.lean)
-/
@[path]
private lemma rectLeftConnection_tangential_measureReal_le_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {z : Site 2}
  {a b c d b' c' d' : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hz : z 0 = 0)
  (hb : b + (z 0 : Real) ≤ b')
  (hc : c' ≤ c + (z 1 : Real))
  (hd : d + (z 1 : Real) ≤ d') :
-- imply
  mu.real (E.rectSideConnectionEvent a b c d S (E.rectLeftBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b' c' d' (P.shift z '' S) (E.rectLeftBoundaryVertices a b' c' d')) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectLeftConnection_tangential_measureReal_le E mu hTI z hz a b c d b' c' d' S hb hc hd

/--
[PeriodicPlaneEmbedding.rectRightConnection_tangential_measureReal_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryGrid.lean)
-/
@[path]
private lemma rectRightConnection_tangential_measureReal_le_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {z : Site 2}
  {a b c d a' c' d' : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hz : z 0 = 0)
  (ha : a' ≤ a + (z 0 : Real))
  (hc : c' ≤ c + (z 1 : Real))
  (hd : d + (z 1 : Real) ≤ d') :
-- imply
  mu.real (E.rectSideConnectionEvent a b c d S (E.rectRightBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a' b c' d' (P.shift z '' S) (E.rectRightBoundaryVertices a' b c' d')) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectRightConnection_tangential_measureReal_le E mu hTI z hz a b c d a' c' d' S ha hc hd

/--
[PeriodicPlaneEmbedding.rectBottomConnection_tangential_measureReal_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryGrid.lean)
-/
@[path]
private lemma rectBottomConnection_tangential_measureReal_le_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {z : Site 2}
  {a b c d a' b' d' : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hz : z 1 = 0)
  (ha : a' ≤ a + (z 0 : Real))
  (hb : b + (z 0 : Real) ≤ b')
  (hd : d + (z 1 : Real) ≤ d') :
-- imply
  mu.real (E.rectSideConnectionEvent a b c d S (E.rectBottomBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a' b' c d' (P.shift z '' S) (E.rectBottomBoundaryVertices a' b' c d')) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectBottomConnection_tangential_measureReal_le E mu hTI z hz a b c d a' b' d' S ha hb hd

/--
[PeriodicPlaneEmbedding.rectTopConnection_tangential_measureReal_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryGrid.lean)
-/
@[path]
private lemma rectTopConnection_tangential_measureReal_le_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {z : Site 2}
  {a b c d a' b' c' : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hz : z 1 = 0)
  (ha : a' ≤ a + (z 0 : Real))
  (hb : b + (z 0 : Real) ≤ b')
  (hc : c' ≤ c + (z 1 : Real)) :
-- imply
  mu.real (E.rectSideConnectionEvent a b c d S (E.rectTopBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a' b' c' d (P.shift z '' S) (E.rectTopBoundaryVertices a' b' c' d)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectTopConnection_tangential_measureReal_le E mu hTI z hz a b c d a' b' c' S ha hb hc


-- created on 2026-10-23
