import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlane.Part4
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.connectedWithinSet_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlane.lean)
-/
@[path]
private lemma connectedWithinSet_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {A : Set V}
  {x y : V} :
-- imply
  MeasurableSet (P.connectedWithinSet A x y) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.connectedWithinSet_measurableSet P A x y

/--
[PeriodicGraph.connectedWithinSet_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlane.lean)
-/
@[path]
private lemma connectedWithinSet_isIncreasing_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {A : Set V}
  {x y : V} :
-- imply
  IsIncreasing (P.connectedWithinSet A x y) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.connectedWithinSet_isIncreasing P A x y

/--
[PeriodicGraph.connectedWithinSet_mono_region](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlane.lean)
-/
@[path]
private lemma connectedWithinSet_mono_region_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {A B : Set V}
  {x y : V}
-- given
  (hAB : A ⊆ B) :
-- imply
  P.connectedWithinSet A x y ⊆ P.connectedWithinSet B x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.connectedWithinSet_mono_region P hAB x y

/--
[PeriodicGraph.connectedWithinSet_configTranslate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlane.lean)
-/
@[path]
private lemma connectedWithinSet_configTranslate_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {omega : ConfigSpace (Sym2 V)}
  {A : Set V}
  {x y : V} :
-- imply
  P.configTranslate z omega ∈ P.connectedWithinSet (P.shift z '' A) (P.shift z x) (P.shift z y) ↔ omega ∈ P.connectedWithinSet A x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.connectedWithinSet_configTranslate P z omega A x y

/--
[PeriodicGraph.setConnectionWithin_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlane.lean)
-/
@[path]
private lemma setConnectionWithin_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {A S T : Set V} :
-- imply
  MeasurableSet (P.setConnectionWithin A S T) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.setConnectionWithin_measurableSet P A S T

/--
[PeriodicGraph.setConnectionWithin_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlane.lean)
-/
@[path]
private lemma setConnectionWithin_isIncreasing_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {A S T : Set V} :
-- imply
  IsIncreasing (P.setConnectionWithin A S T) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.setConnectionWithin_isIncreasing P A S T

/--
[PeriodicGraph.setConnectionWithin_union_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlane.lean)
-/
@[path]
private lemma setConnectionWithin_union_target_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {A S T U : Set V} :
-- imply
  P.setConnectionWithin A S (T ∪ U) = P.setConnectionWithin A S T ∪ P.setConnectionWithin A S U := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.setConnectionWithin_union_target P A S T U

/--
[directional_sqrt_trick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlane.lean)
-/
@[path]
private lemma directional_sqrt_trick_eq
  [DecidableEq V]
  [Countable V]
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {A B : Set (ConfigSpace (Sym2 V))}
-- given
  (hFKG : IsFKG mu)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B)
  (hAm : MeasurableSet A)
  (hBm : MeasurableSet B)
  (hBA : mu.real B ≤ mu.real A) :
-- imply
  1 - Real.sqrt (1 - mu.real (A ∪ B)) ≤ mu.real A := by
-- proof
  apply StatMech.FK.PeriodicPlanar.directional_sqrt_trick mu hFKG hA hB hAm hBm hBA

/--
[three_event_intersection_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlane.lean)
-/
@[path]
private lemma three_event_intersection_lower_bound_eq
  [DecidableEq V]
  [Countable V]
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {A B C : Set (ConfigSpace (Sym2 V))}
-- given
  (hBm : MeasurableSet B)
  (hCm : MeasurableSet C) :
-- imply
  mu.real A + mu.real B + mu.real C - 2 ≤ mu.real ((A ∩ B) ∩ C) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.three_event_intersection_lower_bound mu hBm hCm

/--
[PeriodicPlaneEmbedding.boundary_eq_lower_union_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlane.lean)
-/
@[path]
private lemma boundary_eq_lower_union_upper_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r s : ℝ} :
-- imply
  E.rightHalfPlaneBoundaryVertices r = E.lowerBoundaryRayVertices r s ∪ E.upperBoundaryRayVertices r s := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.boundary_eq_lower_union_upper E r s

/--
[PeriodicPlaneEmbedding.rightHalfPlaneBoundary_coord_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlane.lean)
-/
@[path]
private lemma rightHalfPlaneBoundary_coord_lt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {B r : ℝ}
  {x : V}
-- given
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (hx : x ∈ E.rightHalfPlaneBoundaryVertices r) :
-- imply
  E.vertexCoord x 0 < r + B := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rightHalfPlaneBoundary_coord_lt E hB hx

/--
[PeriodicPlaneEmbedding.lowerBoundaryRay_directional_sqrt_trick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlane.lean)
-/
@[path]
private lemma lowerBoundaryRay_directional_sqrt_trick_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r s : ℝ}
  {S : Set V}
-- given
  (hFKG : IsFKG mu)
  (hcomp : mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r s)) ≤ mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r s))) :
-- imply
  1 - Real.sqrt (1 - mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r))) ≤ mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r s)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.lowerBoundaryRay_directional_sqrt_trick E mu hFKG r s S hcomp

/--
[PeriodicPlaneEmbedding.exists_shift_orbitBox_subset_rightHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlane.lean)
-/
@[path]
private lemma exists_shift_orbitBox_subset_rightHalfPlane_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {N : ℕ}
  {r : ℝ} :
-- imply
  ∃ z : Site 2, ∀ v ∈ P.orbitBox N, P.shift z v ∈ E.rightHalfPlaneVertices r := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_shift_orbitBox_subset_rightHalfPlane E N r

/--
[PeriodicPlaneEmbedding.exists_shift_connectedWithinOrbit_into_rightHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlane.lean)
-/
@[path]
private lemma exists_shift_connectedWithinOrbit_into_rightHalfPlane_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {N : ℕ}
  {r : ℝ} :
-- imply
  ∃ z : Site 2, ∀ (omega : ConfigSpace (Sym2 V)) (x y : V), omega ∈ P.connectedWithinOrbit x y N → P.configTranslate z omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) (P.shift z x) (P.shift z y) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_shift_connectedWithinOrbit_into_rightHalfPlane E N r

/--
[PeriodicPlaneEmbedding.halfPlanePairMergeError_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlane.lean)
-/
@[path]
private lemma halfPlanePairMergeError_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : ℝ}
  {x y : V} :
-- imply
  MeasurableSet (E.halfPlanePairMergeError r x y) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.halfPlanePairMergeError_measurableSet E r x y

/--
[PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeError_preimage_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlane.lean)
-/
@[path]
private lemma exists_shift_halfPlanePairMergeError_preimage_subset_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {N : ℕ}
  {r : ℝ}
  {x y : V} :
-- imply
  ∃ z : Site 2, P.configTranslate z ⁻¹' E.halfPlanePairMergeError r (P.shift z x) (P.shift z y) ⊆ P.pairMergeError x y N := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeError_preimage_subset E N r x y

/--
[PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeError_measureReal_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlane.lean)
-/
@[path]
private lemma exists_shift_halfPlanePairMergeError_measureReal_le_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {N : ℕ}
  {r : ℝ}
  {x y : V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  ∃ z : Site 2, mu.real (E.halfPlanePairMergeError r (P.shift z x) (P.shift z y)) ≤ mu.real (P.pairMergeError x y N) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeError_measureReal_le E mu hTI N r x y

/--
[PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeError_measureReal_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlane.lean)
-/
@[path]
private lemma exists_shift_halfPlanePairMergeError_measureReal_lt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : ℝ}
  {x y : V}
  {ε : ℝ}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hε : 0 < ε) :
-- imply
  ∃ z : Site 2, mu.real (E.halfPlanePairMergeError r (P.shift z x) (P.shift z y)) < ε := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeError_measureReal_lt E mu hTI hunique r x y hε


-- created on 2026-10-23
