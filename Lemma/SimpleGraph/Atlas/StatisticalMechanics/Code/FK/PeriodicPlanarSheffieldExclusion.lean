import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldExclusion
open Filter MeasureTheory Set Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.image_subset_fourShiftTemplate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldExclusion.lean)
-/
@[path]
private lemma image_subset_fourShiftTemplate_eq
  [Countable V]
  [Countable W]
  {P : PeriodicGraph V}
  {S : Finset V}
  {zLeft zRight zBottom zTop : Site 2} :
-- imply
  S.image (P.shift zLeft) ⊆ P.fourShiftTemplate S zLeft zRight zBottom zTop := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.image_subset_fourShiftTemplate P S zLeft zRight zBottom zTop

/--
[PeriodicGraph.image_right_subset_fourShiftTemplate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldExclusion.lean)
-/
@[path]
private lemma image_right_subset_fourShiftTemplate_eq
  [Countable V]
  [Countable W]
  {P : PeriodicGraph V}
  {S : Finset V}
  {zLeft zRight zBottom zTop : Site 2} :
-- imply
  S.image (P.shift zRight) ⊆ P.fourShiftTemplate S zLeft zRight zBottom zTop := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.image_right_subset_fourShiftTemplate P S zLeft zRight zBottom zTop

/--
[PeriodicGraph.image_bottom_subset_fourShiftTemplate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldExclusion.lean)
-/
@[path]
private lemma image_bottom_subset_fourShiftTemplate_eq
  [Countable V]
  [Countable W]
  {P : PeriodicGraph V}
  {S : Finset V}
  {zLeft zRight zBottom zTop : Site 2} :
-- imply
  S.image (P.shift zBottom) ⊆ P.fourShiftTemplate S zLeft zRight zBottom zTop := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.image_bottom_subset_fourShiftTemplate P S zLeft zRight zBottom zTop

/--
[PeriodicGraph.image_top_subset_fourShiftTemplate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldExclusion.lean)
-/
@[path]
private lemma image_top_subset_fourShiftTemplate_eq
  [Countable V]
  [Countable W]
  {P : PeriodicGraph V}
  {S : Finset V}
  {zLeft zRight zBottom zTop : Site 2} :
-- imply
  S.image (P.shift zTop) ⊆ P.fourShiftTemplate S zLeft zRight zBottom zTop := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.image_top_subset_fourShiftTemplate P S zLeft zRight zBottom zTop

/--
[PeriodicPlaneEmbedding.rectSideConnectionEvent_mono_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldExclusion.lean)
-/
@[path]
private lemma rectSideConnectionEvent_mono_source_eq
  [Countable V]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {S T side : Set V}
-- given
  (hST : S ⊆ T) :
-- imply
  E.rectSideConnectionEvent a b c d S side ⊆ E.rectSideConnectionEvent a b c d T side := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectSideConnectionEvent_mono_source E hST

/--
[PeriodicPlaneEmbedding.fourShiftTemplate_preferenceGrid_subset_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldExclusion.lean)
-/
@[path]
private lemma fourShiftTemplate_preferenceGrid_subset_rect_eq
  [Countable V]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {S : Finset V}
  {zLeft zRight zBottom zTop : Site 2}
-- given
  (M width height : Nat)
  (hleft : (S.image (P.shift zLeft) : Set V) ⊆ E.rectVertices (-(M : Real)) (M : Real) (-(M : Real)) (M : Real))
  (hright : (S.image (P.shift zRight) : Set V) ⊆ E.rectVertices (-(M : Real)) (M : Real) (-(M : Real)) (M : Real))
  (hbottom : (S.image (P.shift zBottom) : Set V) ⊆ E.rectVertices (-(M : Real)) (M : Real) (-(M : Real)) (M : Real))
  (htop : (S.image (P.shift zTop) : Set V) ⊆ E.rectVertices (-(M : Real)) (M : Real) (-(M : Real)) (M : Real)) :
-- imply
  ∀ v : PreferenceGridVertex width height, ((P.fourShiftTemplate S zLeft zRight zBottom zTop).image (P.shift (preferenceGridSite v)) : Set V) ⊆ E.rectVertices (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.fourShiftTemplate_preferenceGrid_subset_rect E M width height S zLeft zRight zBottom zTop hleft hright hbottom htop

/--
[PeriodicPlaneEmbedding.preferenceGrid_orbitBox_subset_rect_of_coordinateBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldExclusion.lean)
-/
@[path]
private lemma preferenceGrid_orbitBox_subset_rect_of_coordinateBound_eq
  [Countable V]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
-- given
  (R M width height : Nat)
  (hx : E.orbitBoxCoordinateBound R (0 : Fin 2) ≤ M)
  (hy : E.orbitBoxCoordinateBound R (1 : Fin 2) ≤ M) :
-- imply
  ∀ v : PreferenceGridVertex width height, P.shift (preferenceGridSite v) '' (P.orbitBox R : Set V) ⊆ E.rectVertices (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.preferenceGrid_orbitBox_subset_rect_of_coordinateBound E R M width height hx hy

/--
[PeriodicPlaneEmbedding.rectBottomConnection_fourShiftTemplate_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldExclusion.lean)
-/
@[path]
private lemma rectBottomConnection_fourShiftTemplate_le_eq
  [Countable V]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {S : Finset V}
  {zLeft zRight zBottom zTop : Site 2}
  {i : Fin (width + 1)}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (M width height : Nat) :
-- imply
  mu.real (E.rectSideConnectionEvent (-(M : Real)) (M : Real) (-(M : Real)) (M : Real) (S.image (P.shift zBottom) : Set V) (E.rectBottomBoundaryVertices (-(M : Real)) (M : Real) (-(M : Real)) (M : Real))) ≤ mu.real (E.rectSideConnectionEvent (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real) ((P.fourShiftTemplate S zLeft zRight zBottom zTop).image (P.shift (preferenceGridSite (i, (0 : Fin (height + 1))))) : Set V) (E.rectBottomBoundaryVertices (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectBottomConnection_fourShiftTemplate_le E mu hTI M width height S zLeft zRight zBottom zTop i

/--
[PeriodicPlaneEmbedding.rectLeftConnection_fourShiftTemplate_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldExclusion.lean)
-/
@[path]
private lemma rectLeftConnection_fourShiftTemplate_le_eq
  [Countable V]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {S : Finset V}
  {zLeft zRight zBottom zTop : Site 2}
  {j : Fin (height + 1)}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (M width height : Nat) :
-- imply
  mu.real (E.rectSideConnectionEvent (-(M : Real)) (M : Real) (-(M : Real)) (M : Real) (S.image (P.shift zLeft) : Set V) (E.rectLeftBoundaryVertices (-(M : Real)) (M : Real) (-(M : Real)) (M : Real))) ≤ mu.real (E.rectSideConnectionEvent (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real) ((P.fourShiftTemplate S zLeft zRight zBottom zTop).image (P.shift (preferenceGridSite ((0 : Fin (width + 1)), j))) : Set V) (E.rectLeftBoundaryVertices (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectLeftConnection_fourShiftTemplate_le E mu hTI M width height S zLeft zRight zBottom zTop j

/--
[PeriodicPlaneEmbedding.rectRightConnection_fourShiftTemplate_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldExclusion.lean)
-/
@[path]
private lemma rectRightConnection_fourShiftTemplate_le_eq
  [Countable V]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {S : Finset V}
  {zLeft zRight zBottom zTop : Site 2}
  {j : Fin (height + 1)}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (M width height : Nat) :
-- imply
  mu.real (E.rectSideConnectionEvent (-(M : Real)) (M : Real) (-(M : Real)) (M : Real) (S.image (P.shift zRight) : Set V) (E.rectRightBoundaryVertices (-(M : Real)) (M : Real) (-(M : Real)) (M : Real))) ≤ mu.real (E.rectSideConnectionEvent (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real) ((P.fourShiftTemplate S zLeft zRight zBottom zTop).image (P.shift (preferenceGridSite (Fin.last width, j))) : Set V) (E.rectRightBoundaryVertices (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectRightConnection_fourShiftTemplate_le E mu hTI M width height S zLeft zRight zBottom zTop j

/--
[PeriodicPlaneEmbedding.rectTopConnection_fourShiftTemplate_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldExclusion.lean)
-/
@[path]
private lemma rectTopConnection_fourShiftTemplate_le_eq
  [Countable V]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {S : Finset V}
  {zLeft zRight zBottom zTop : Site 2}
  {i : Fin (width + 1)}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (M width height : Nat) :
-- imply
  mu.real (E.rectSideConnectionEvent (-(M : Real)) (M : Real) (-(M : Real)) (M : Real) (S.image (P.shift zTop) : Set V) (E.rectTopBoundaryVertices (-(M : Real)) (M : Real) (-(M : Real)) (M : Real))) ≤ mu.real (E.rectSideConnectionEvent (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real) ((P.fourShiftTemplate S zLeft zRight zBottom zTop).image (P.shift (preferenceGridSite (i, Fin.last height))) : Set V) (E.rectTopBoundaryVertices (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectTopConnection_fourShiftTemplate_le E mu hTI M width height S zLeft zRight zBottom zTop i

/--
[PeriodicGraph.fourShiftTemplate_hitsInfinite_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldExclusion.lean)
-/
@[path]
private lemma fourShiftTemplate_hitsInfinite_tendsto_one_eq
  [Countable V]
  [Countable W]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {zLeft zRight zBottom zTop : Nat → Site 2}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hexists : mu {omega | P.HasInfiniteCluster omega} = 1) :
-- imply
  Tendsto (fun n => mu.real (P.setHitsInfinite (P.fourShiftTemplate (P.orbitBox n) (zLeft n) (zRight n) (zBottom n) (zTop n) : Set V))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.fourShiftTemplate_hitsInfinite_tendsto_one P mu hTI hexists zLeft zRight zBottom zTop

/--
[isFKG_decreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldExclusion.lean)
-/
@[path]
private lemma isFKG_decreasing_eq
  [Countable V]
  [Countable W]
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {A B : Set (ConfigSpace (Sym2 V))}
-- given
  (hFKG : IsFKG mu)
  (hA : IsDecreasing A)
  (hB : IsDecreasing B)
  (hAm : MeasurableSet A)
  (hBm : MeasurableSet B) :
-- imply
  mu.real A * mu.real B <= mu.real (A ∩ B) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.isFKG_decreasing mu hFKG hA hB hAm hBm

/--
[dualConfigEquiv_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldExclusion.lean)
-/
@[path]
private lemma dualConfigEquiv_antitone_eq
  [Countable V]
  [Countable W]
  {edgeDual : Sym2 V ≃ Sym2 W} :
-- imply
  Antitone (dualConfigEquiv edgeDual) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.dualConfigEquiv_antitone edgeDual

/--
[PeriodicPlanarDualPair.dualMeasure_isFKG](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldExclusion.lean)
-/
@[path]
private lemma dualMeasure_isFKG_eq
  [Countable V]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hFKG : IsFKG mu) :
-- imply
  IsFKG (D.dualMeasure mu) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualMeasure_isFKG D mu hFKG

/--
[PeriodicPlanarDualPair.primalUnique_measure_eq_one_of_common](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldExclusion.lean)
-/
@[path]
private lemma primalUnique_measure_eq_one_of_common_eq
  [Countable V]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hcommon : mu D.commonUniqueInfiniteClusterEvent = 1) :
-- imply
  mu {omega | P.HasUniqueInfiniteCluster omega} = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.primalUnique_measure_eq_one_of_common D mu hcommon

/--
[PeriodicPlanarDualPair.dualUnique_measure_eq_one_of_common](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldExclusion.lean)
-/
@[path]
private lemma dualUnique_measure_eq_one_of_common_eq
  [Countable V]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hcommon : mu D.commonUniqueInfiniteClusterEvent = 1) :
-- imply
  D.dualMeasure mu {eta | Pdual.HasUniqueInfiniteCluster eta} = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualUnique_measure_eq_one_of_common D mu hcommon

/--
[PeriodicPlanarDualPair.freeBufferedInfiniteVolume_sheffieldData_of_common](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldExclusion.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_sheffieldData_of_common_eq
  [Countable V]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hcommon : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent = 1) :
-- imply
  let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) IsFKG mu ∧ P.IsTranslationInvariant mu ∧ IsFKG (D.dualMeasure mu) ∧ Pdual.IsTranslationInvariant (D.dualMeasure mu) ∧ mu {omega | P.HasUniqueInfiniteCluster omega} = 1 ∧ D.dualMeasure mu {eta | Pdual.HasUniqueInfiniteCluster eta} = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeBufferedInfiniteVolume_sheffieldData_of_common D hp hp1 hq hcommon

/--
[PeriodicPlaneEmbedding.exists_uniformTemplate_boundaryLimits_crossing_max_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldExclusion.lean)
-/
@[path]
private lemma exists_uniformTemplate_boundaryLimits_crossing_max_tendsto_one_eq
  [Countable V]
  [Countable W]
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
  ∃ radius : Nat → Nat, ∀ (width height : Nat → Nat) (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n) (base : Nat → Site 2) (a b c d : Nat → Real) (bottom top left right : (n : Nat) → PreferenceGridVertex (width n) (height n) → Real) (pBottom pTop pLeft pRight : Nat → Real), (∀ n (v : PreferenceGridVertex (width n) (height n)), ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) ⊆ E.rectVertices (a n) (b n) (c n) (d n)) → (∀ n (v : PreferenceGridVertex (width n) (height n)), (P.shift (base n + preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a n) (b n) (c n) (d n)) → (∀ n v, bottom n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n v, top n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n v, left n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n v, right n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n, pBottom n ≤ 1) → (∀ n, pTop n ≤ 1) → (∀ n, pLeft n ≤ 1) → (∀ n, pRight n ≤ 1) → (∀ n (i : Fin (width n + 1)), pBottom n ≤ bottom n (i, 0)) → (∀ n (i : Fin (width n + 1)), pTop n ≤ top n (i, Fin.last (height n))) → (∀ n (j : Fin (height n + 1)), pLeft n ≤ left n (0, j)) → (∀ n (j : Fin (height n + 1)), pRight n ≤ right n (Fin.last (width n), j)) → Tendsto pBottom atTop (nhds 1) → Tendsto pTop atTop (nhds 1) → Tendsto pLeft atTop (nhds 1) → Tendsto pRight atTop (nhds 1) → Tendsto (fun n => max (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n))) (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformTemplate_boundaryLimits_crossing_max_tendsto_one E mu hFKG hTI hunique template htemplateHit

/--
[PeriodicPlaneEmbedding.exists_fourShiftTemplate_crossing_max_tendsto_one_of_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldExclusion.lean)
-/
@[path]
private lemma exists_fourShiftTemplate_crossing_max_tendsto_one_of_connector_eq
  [Countable V]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {M : Nat → Nat}
  {zLeft zRight zBottom zTop : Nat → Site 2}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hleft : ∀ n, ((P.orbitBox n).image (P.shift (zLeft n)) : Set V) ⊆ E.rectVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real))
  (hright : ∀ n, ((P.orbitBox n).image (P.shift (zRight n)) : Set V) ⊆ E.rectVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real))
  (hbottom : ∀ n, ((P.orbitBox n).image (P.shift (zBottom n)) : Set V) ⊆ E.rectVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real))
  (htop : ∀ n, ((P.orbitBox n).image (P.shift (zTop n)) : Set V) ⊆ E.rectVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real))
  (hleftLimit : Tendsto (fun n => mu.real (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real) ((P.orbitBox n).image (P.shift (zLeft n)) : Set V) (E.rectLeftBoundaryVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
  (hrightLimit : Tendsto (fun n => mu.real (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real) ((P.orbitBox n).image (P.shift (zRight n)) : Set V) (E.rectRightBoundaryVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
  (hbottomLimit : Tendsto (fun n => mu.real (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real) ((P.orbitBox n).image (P.shift (zBottom n)) : Set V) (E.rectBottomBoundaryVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
  (htopLimit : Tendsto (fun n => mu.real (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real) ((P.orbitBox n).image (P.shift (zTop n)) : Set V) (E.rectTopBoundaryVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real)))) atTop (nhds 1)) :
-- imply
  ∃ radius : Nat → Nat, ∀ (width height : Nat → Nat) (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n), (∀ n (v : PreferenceGridVertex (width n) (height n)), (P.shift (preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (-(M n : Real)) (M n + width n : Real) (-(M n : Real)) (M n + height n : Real)) → Tendsto (fun n => max (mu.real (E.verticalCrossingEvent (-(M n : Real)) (M n + width n : Real) (-(M n : Real)) (M n + height n : Real))) (mu.real (E.horizontalCrossingEvent (-(M n : Real)) (M n + width n : Real) (-(M n : Real)) (M n + height n : Real)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_fourShiftTemplate_crossing_max_tendsto_one_of_connector E mu hFKG hTI hunique M zLeft zRight zBottom zTop hleft hright hbottom htop hleftLimit hrightLimit hbottomLimit htopLimit

/--
[PeriodicPlaneEmbedding.exists_fourShiftTemplate_crossing_max_tendsto_one_of_coordinateBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldExclusion.lean)
-/
@[path]
private lemma exists_fourShiftTemplate_crossing_max_tendsto_one_of_coordinateBounds_eq
  [Countable V]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {M : Nat → Nat}
  {zLeft zRight zBottom zTop : Nat → Site 2}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hleft : ∀ n, ((P.orbitBox n).image (P.shift (zLeft n)) : Set V) ⊆ E.rectVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real))
  (hright : ∀ n, ((P.orbitBox n).image (P.shift (zRight n)) : Set V) ⊆ E.rectVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real))
  (hbottom : ∀ n, ((P.orbitBox n).image (P.shift (zBottom n)) : Set V) ⊆ E.rectVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real))
  (htop : ∀ n, ((P.orbitBox n).image (P.shift (zTop n)) : Set V) ⊆ E.rectVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real))
  (hleftLimit : Tendsto (fun n => mu.real (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real) ((P.orbitBox n).image (P.shift (zLeft n)) : Set V) (E.rectLeftBoundaryVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
  (hrightLimit : Tendsto (fun n => mu.real (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real) ((P.orbitBox n).image (P.shift (zRight n)) : Set V) (E.rectRightBoundaryVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
  (hbottomLimit : Tendsto (fun n => mu.real (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real) ((P.orbitBox n).image (P.shift (zBottom n)) : Set V) (E.rectBottomBoundaryVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
  (htopLimit : Tendsto (fun n => mu.real (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real) ((P.orbitBox n).image (P.shift (zTop n)) : Set V) (E.rectTopBoundaryVertices (-(M n : Real)) (M n : Real) (-(M n : Real)) (M n : Real)))) atTop (nhds 1)) :
-- imply
  ∃ radius : Nat → Nat, ∀ (width height : Nat → Nat) (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n), (∀ n, E.orbitBoxCoordinateBound (P.bufferedRadius (radius n)) (0 : Fin 2) ≤ M n) → (∀ n, E.orbitBoxCoordinateBound (P.bufferedRadius (radius n)) (1 : Fin 2) ≤ M n) → Tendsto (fun n => max (mu.real (E.verticalCrossingEvent (-(M n : Real)) (M n + width n : Real) (-(M n : Real)) (M n + height n : Real))) (mu.real (E.horizontalCrossingEvent (-(M n : Real)) (M n + width n : Real) (-(M n : Real)) (M n + height n : Real)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_fourShiftTemplate_crossing_max_tendsto_one_of_coordinateBounds E mu hFKG hTI hunique M zLeft zRight zBottom zTop hleft hright hbottom htop hleftLimit hrightLimit hbottomLimit htopLimit

/--
[PeriodicPlaneEmbedding.exists_commonSquare_fourShift_crossing_max_tendsto_one_of_coordinateBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldExclusion.lean)
-/
@[path]
private lemma exists_commonSquare_fourShift_crossing_max_tendsto_one_of_coordinateBounds_eq
  [Countable V]
  [Countable W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
-- imply
  ∃ (M : Nat → Nat) (zLeft zRight zBottom zTop : Nat → Site 2) (radius : Nat → Nat), ∀ (width height : Nat → Nat) (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n), (∀ n, E.orbitBoxCoordinateBound (P.bufferedRadius (radius n)) (0 : Fin 2) ≤ M n) → (∀ n, E.orbitBoxCoordinateBound (P.bufferedRadius (radius n)) (1 : Fin 2) ≤ M n) → Tendsto (fun n => max (mu.real (E.verticalCrossingEvent (-(M n : Real)) (M n + width n : Real) (-(M n : Real)) (M n + height n : Real))) (mu.real (E.horizontalCrossingEvent (-(M n : Real)) (M n + width n : Real) (-(M n : Real)) (M n + height n : Real)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_commonSquare_fourShift_crossing_max_tendsto_one_of_coordinateBounds E mu hFKG hTI hunique

/--
[PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_zero_or_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldExclusion.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_commonUnique_measure_zero_or_one_eq
  [Countable V]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent = 0 ∨ mu D.commonUniqueInfiniteClusterEvent = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_zero_or_one D hp hp1 hq

/--
[PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_eq_zero_iff_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldExclusion.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_commonUnique_measure_eq_zero_iff_ne_one_eq
  [Countable V]
  [Countable W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent = 0 ↔ mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_eq_zero_iff_ne_one D hp hp1 hq


-- created on 2026-10-23
