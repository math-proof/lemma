import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneStrip.Part3
open Filter MeasureTheory Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.setConnectionWithin_mono_region](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStrip.lean)
-/
@[path]
private lemma setConnectionWithin_mono_region_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {A B : Set V}
  {S T : Set V}
-- given
  (hAB : A ⊆ B) :
-- imply
  P.setConnectionWithin A S T ⊆ P.setConnectionWithin B S T := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.setConnectionWithin_mono_region P hAB S T

/--
[PeriodicPlaneEmbedding.rightHalfPlaneStripVertices_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStrip.lean)
-/
@[path]
private lemma rightHalfPlaneStripVertices_subset_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {n : Nat} :
-- imply
  E.rightHalfPlaneStripVertices r n ⊆ E.rightHalfPlaneVertices r := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rightHalfPlaneStripVertices_subset E r n

/--
[PeriodicPlaneEmbedding.rightHalfPlaneStripVertices_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStrip.lean)
-/
@[path]
private lemma rightHalfPlaneStripVertices_mono_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real} :
-- imply
  Monotone (E.rightHalfPlaneStripVertices r) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rightHalfPlaneStripVertices_mono E r

/--
[PeriodicPlaneEmbedding.connectedWithin_rightHalfPlane_exists_strip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStrip.lean)
-/
@[path]
private lemma connectedWithin_rightHalfPlane_exists_strip_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {omega : ConfigSpace (Sym2 V)}
  {r : Real}
  {x y : V}
-- given
  (hxy : omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) x y) :
-- imply
  ∃ n : Nat, omega ∈ P.connectedWithinSet (E.rightHalfPlaneStripVertices r n) x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.connectedWithin_rightHalfPlane_exists_strip E omega r x y hxy

/--
[PeriodicPlaneEmbedding.iUnion_connectedWithin_rightHalfPlaneStrip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStrip.lean)
-/
@[path]
private lemma iUnion_connectedWithin_rightHalfPlaneStrip_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {x y : V} :
-- imply
  (⋃ n : Nat, P.connectedWithinSet (E.rightHalfPlaneStripVertices r n) x y) = P.connectedWithinSet (E.rightHalfPlaneVertices r) x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.iUnion_connectedWithin_rightHalfPlaneStrip E r x y

/--
[PeriodicPlaneEmbedding.setConnectionWithin_rightHalfPlaneStrip_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStrip.lean)
-/
@[path]
private lemma setConnectionWithin_rightHalfPlaneStrip_mono_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {S T : Set V} :
-- imply
  Monotone (fun n : Nat => P.setConnectionWithin (E.rightHalfPlaneStripVertices r n) S T) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.setConnectionWithin_rightHalfPlaneStrip_mono E r S T

/--
[PeriodicPlaneEmbedding.iUnion_setConnectionWithin_rightHalfPlaneStrip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStrip.lean)
-/
@[path]
private lemma iUnion_setConnectionWithin_rightHalfPlaneStrip_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {S T : Set V} :
-- imply
  (⋃ n : Nat, P.setConnectionWithin (E.rightHalfPlaneStripVertices r n) S T) = P.setConnectionWithin (E.rightHalfPlaneVertices r) S T := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.iUnion_setConnectionWithin_rightHalfPlaneStrip E r S T

/--
[PeriodicPlaneEmbedding.rightHalfPlaneStrip_connection_measureReal_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStrip.lean)
-/
@[path]
private lemma rightHalfPlaneStrip_connection_measureReal_tendsto_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r : Real}
  {S T : Set V} :
-- imply
  Tendsto (fun n : Nat => mu.real (P.setConnectionWithin (E.rightHalfPlaneStripVertices r n) S T)) atTop (nhds (mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S T))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rightHalfPlaneStrip_connection_measureReal_tendsto E mu r S T

/--
[PeriodicPlaneEmbedding.halfPlaneStripPairMergeError_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStrip.lean)
-/
@[path]
private lemma halfPlaneStripPairMergeError_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {n : Nat}
  {x y : V} :
-- imply
  MeasurableSet (E.halfPlaneStripPairMergeError r n x y) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.halfPlaneStripPairMergeError_measurableSet E r n x y

/--
[PeriodicPlaneEmbedding.halfPlaneStripPairMergeError_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStrip.lean)
-/
@[path]
private lemma halfPlaneStripPairMergeError_antitone_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {x y : V} :
-- imply
  Antitone (fun n => E.halfPlaneStripPairMergeError r n x y) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.halfPlaneStripPairMergeError_antitone E r x y

/--
[PeriodicPlaneEmbedding.iInter_halfPlaneStripPairMergeError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStrip.lean)
-/
@[path]
private lemma iInter_halfPlaneStripPairMergeError_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real}
  {x y : V} :
-- imply
  (⋂ n : Nat, E.halfPlaneStripPairMergeError r n x y) = E.halfPlanePairMergeError r x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.iInter_halfPlaneStripPairMergeError E r x y

/--
[PeriodicPlaneEmbedding.halfPlaneStripPairMergeError_measureReal_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStrip.lean)
-/
@[path]
private lemma halfPlaneStripPairMergeError_measureReal_tendsto_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r : Real}
  {x y : V} :
-- imply
  Tendsto (fun n => mu.real (E.halfPlaneStripPairMergeError r n x y)) atTop (nhds (mu.real (E.halfPlanePairMergeError r x y))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.halfPlaneStripPairMergeError_measureReal_tendsto E mu r x y

/--
[PeriodicPlaneEmbedding.exists_shift_stripPairMergeError_measureReal_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStrip.lean)
-/
@[path]
private lemma exists_shift_stripPairMergeError_measureReal_lt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : Real}
  {x y : V}
  {epsilon : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ z : Site 2, ∃ n : Nat, mu.real (E.halfPlaneStripPairMergeError r n (P.shift z x) (P.shift z y)) < epsilon := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_shift_stripPairMergeError_measureReal_lt E mu hTI hunique r x y hepsilon


-- created on 2026-10-23
