import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCluster.Part8
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.axisSwap_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma axisSwap_isErgodic_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
-- given
  (hErgodic : P.IsErgodic mu) :
-- imply
  P.axisSwap.IsErgodic mu := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.axisSwap_isErgodic P mu hErgodic

/--
[PeriodicGraph.axisNeg_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma axisNeg_isErgodic_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
-- given
  (hErgodic : P.IsErgodic mu) :
-- imply
  P.axisNeg.IsErgodic mu := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.axisNeg_isErgodic P mu hErgodic

/--
[PeriodicGraph.mem_clusterWithinSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma mem_clusterWithinSet_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {A : Set V}
  {x y : V} :
-- imply
  y ∈ P.clusterWithinSet omega A x ↔ omega ∈ P.connectedWithinSet A x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.mem_clusterWithinSet P omega A x y

/--
[PeriodicGraph.iUnion_connectedWithinSet_inter_orbitBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma iUnion_connectedWithinSet_inter_orbitBox_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {A : Set V}
  {x y : V} :
-- imply
  (⋃ n : Nat, P.connectedWithinSet (A ∩ (P.orbitBox n : Set V)) x y) = P.connectedWithinSet A x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.iUnion_connectedWithinSet_inter_orbitBox P A x y

/--
[PeriodicGraph.iUnion_setConnectionWithin_inter_orbitBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma iUnion_setConnectionWithin_inter_orbitBox_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {A S T : Set V} :
-- imply
  (⋃ n : Nat, P.setConnectionWithin (A ∩ (P.orbitBox n : Set V)) S T) = P.setConnectionWithin A S T := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.iUnion_setConnectionWithin_inter_orbitBox P A S T

/--
[PeriodicGraph.setConnectionWithin_inter_orbitBox_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma setConnectionWithin_inter_orbitBox_mono_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {A S T : Set V} :
-- imply
  Monotone (fun n => P.setConnectionWithin (A ∩ (P.orbitBox n : Set V)) S T) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.setConnectionWithin_inter_orbitBox_mono P A S T

/--
[PeriodicGraph.setConnectionWithin_inter_orbitBox_measureReal_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma setConnectionWithin_inter_orbitBox_measureReal_tendsto_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {A S T : Set V} :
-- imply
  Tendsto (fun n => mu.real (P.setConnectionWithin (A ∩ (P.orbitBox n : Set V)) S T)) atTop (nhds (mu.real (P.setConnectionWithin A S T))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.setConnectionWithin_inter_orbitBox_measureReal_tendsto P mu A S T

/--
[PeriodicGraph.clusterWithinSet_configTranslate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma clusterWithinSet_configTranslate_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {omega : ConfigSpace (Sym2 V)}
  {A : Set V}
  {x : V} :
-- imply
  P.shift z '' P.clusterWithinSet omega A x = P.clusterWithinSet (P.configTranslate z omega) (P.shift z '' A) (P.shift z x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.clusterWithinSet_configTranslate P z omega A x

/--
[PeriodicGraph.clusterWithinSet_infinite_iff_orbitBox_escape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma clusterWithinSet_infinite_iff_orbitBox_escape_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {A : Set V}
  {x : V} :
-- imply
  (P.clusterWithinSet omega A x).Infinite ↔ ∀ n : Nat, ∃ y : V, y ∉ (P.orbitBox n : Set V) ∧ omega ∈ P.connectedWithinSet A x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.clusterWithinSet_infinite_iff_orbitBox_escape P omega A x

/--
[PeriodicGraph.measurableSet_clusterWithinSet_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma measurableSet_clusterWithinSet_infinite_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {A : Set V}
  {x : V} :
-- imply
  MeasurableSet {omega : ConfigSpace (Sym2 V) | (P.clusterWithinSet omega A x).Infinite} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.measurableSet_clusterWithinSet_infinite P A x

/--
[PeriodicGraph.clusterWithinSetEscape_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma clusterWithinSetEscape_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {A : Set V}
  {x : V}
  {n : Nat} :
-- imply
  MeasurableSet (P.clusterWithinSetEscape A x n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.clusterWithinSetEscape_measurableSet P A x n

/--
[PeriodicGraph.clusterWithinSetEscape_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma clusterWithinSetEscape_antitone_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {A : Set V}
  {x : V} :
-- imply
  Antitone (P.clusterWithinSetEscape A x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.clusterWithinSetEscape_antitone P A x

/--
[PeriodicGraph.iInter_clusterWithinSetEscape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma iInter_clusterWithinSetEscape_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {A : Set V}
  {x : V} :
-- imply
  (⋂ n : Nat, P.clusterWithinSetEscape A x n) = {omega : ConfigSpace (Sym2 V) | (P.clusterWithinSet omega A x).Infinite} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.iInter_clusterWithinSetEscape P A x

/--
[PeriodicGraph.clusterWithinSetEscape_measureReal_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma clusterWithinSetEscape_measureReal_tendsto_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {A : Set V}
  {x : V} :
-- imply
  Tendsto (fun n => mu.real (P.clusterWithinSetEscape A x n)) atTop (nhds (mu.real {omega : ConfigSpace (Sym2 V) | (P.clusterWithinSet omega A x).Infinite})) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.clusterWithinSetEscape_measureReal_tendsto P mu A x

/--
[PeriodicGraph.hasInfiniteClusterWithin_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma hasInfiniteClusterWithin_mono_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {A B : Set V}
-- given
  (hAB : A ⊆ B) :
-- imply
  P.HasInfiniteClusterWithin omega A → P.HasInfiniteClusterWithin omega B := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.hasInfiniteClusterWithin_mono P omega hAB

/--
[PeriodicGraph.hasInfiniteClusterWithin_configTranslate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma hasInfiniteClusterWithin_configTranslate_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {omega : ConfigSpace (Sym2 V)}
  {A : Set V} :
-- imply
  P.HasInfiniteClusterWithin (P.configTranslate z omega) (P.shift z '' A) ↔ P.HasInfiniteClusterWithin omega A := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.hasInfiniteClusterWithin_configTranslate P z omega A

/--
[PeriodicGraph.measurableSet_hasInfiniteClusterWithin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma measurableSet_hasInfiniteClusterWithin_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {A : Set V} :
-- imply
  MeasurableSet {omega : ConfigSpace (Sym2 V) | P.HasInfiniteClusterWithin omega A} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.measurableSet_hasInfiniteClusterWithin P A

/--
[PeriodicGraph.setHitsInfiniteWithin_configTranslate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma setHitsInfiniteWithin_configTranslate_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {omega : ConfigSpace (Sym2 V)}
  {A S : Set V} :
-- imply
  P.configTranslate z omega ∈ P.setHitsInfiniteWithin (P.shift z '' A) (P.shift z '' S) ↔ omega ∈ P.setHitsInfiniteWithin A S := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.setHitsInfiniteWithin_configTranslate P z omega A S

/--
[PeriodicGraph.setHitsInfiniteWithin_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma setHitsInfiniteWithin_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {A S : Set V} :
-- imply
  MeasurableSet (P.setHitsInfiniteWithin A S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.setHitsInfiniteWithin_measurableSet P A S

/--
[PeriodicGraph.setHitsInfiniteWithin_translate_measureReal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma setHitsInfiniteWithin_translate_measureReal_eq_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {z : Site 2}
  {A S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu.real (P.setHitsInfiniteWithin (P.shift z '' A) (P.shift z '' S)) = mu.real (P.setHitsInfiniteWithin A S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.setHitsInfiniteWithin_translate_measureReal_eq P mu hTI z A S

/--
[PeriodicPlaneEmbedding.shift_image_rightHalfPlaneVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma shift_image_rightHalfPlaneVertices_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {z : Site 2}
  {r : Real} :
-- imply
  P.shift z '' E.rightHalfPlaneVertices r = E.rightHalfPlaneVertices (r + z 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.shift_image_rightHalfPlaneVertices E z r

/--
[PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_translate_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma rightHalfPlaneHasInfiniteCluster_translate_preimage_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {z : Site 2}
  {r : Real} :
-- imply
  P.configTranslate z ⁻¹' E.rightHalfPlaneHasInfiniteCluster (r + z 0) = E.rightHalfPlaneHasInfiniteCluster r := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_translate_preimage E z r

/--
[PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma rightHalfPlaneHasInfiniteCluster_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real} :
-- imply
  MeasurableSet (E.rightHalfPlaneHasInfiniteCluster r) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measurableSet E r

/--
[PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma rightHalfPlaneHasInfiniteCluster_antitone_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P} :
-- imply
  Antitone E.rightHalfPlaneHasInfiniteCluster := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_antitone E

/--
[PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma rightHalfPlaneHasInfiniteCluster_measure_eq_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {z : Site 2}
  {r : Real}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu (E.rightHalfPlaneHasInfiniteCluster (r + z 0)) = mu (E.rightHalfPlaneHasInfiniteCluster r) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq E mu hTI z r

/--
[PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma rightHalfPlaneHasInfiniteCluster_measure_eq_boundary_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {r s : Real}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu (E.rightHalfPlaneHasInfiniteCluster r) = mu (E.rightHalfPlaneHasInfiniteCluster s) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq_boundary E mu hTI r s

/--
[PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteClusterAtInfinity_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma rightHalfPlaneHasInfiniteClusterAtInfinity_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P} :
-- imply
  MeasurableSet E.rightHalfPlaneHasInfiniteClusterAtInfinity := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteClusterAtInfinity_measurableSet E

/--
[PeriodicPlaneEmbedding.mem_rightHalfPlaneHasInfiniteClusterAtInfinity_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma mem_rightHalfPlaneHasInfiniteClusterAtInfinity_iff_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  omega ∈ E.rightHalfPlaneHasInfiniteClusterAtInfinity ↔ ∀ r : Real, omega ∈ E.rightHalfPlaneHasInfiniteCluster r := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.mem_rightHalfPlaneHasInfiniteClusterAtInfinity_iff E omega

/--
[PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteClusterAtInfinity_translate_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma rightHalfPlaneHasInfiniteClusterAtInfinity_translate_preimage_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {z : Site 2} :
-- imply
  P.configTranslate z ⁻¹' E.rightHalfPlaneHasInfiniteClusterAtInfinity = E.rightHalfPlaneHasInfiniteClusterAtInfinity := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteClusterAtInfinity_translate_preimage E z

/--
[PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteClusterAtInfinity_measure_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma rightHalfPlaneHasInfiniteClusterAtInfinity_measure_eq_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r : Real}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu E.rightHalfPlaneHasInfiniteClusterAtInfinity = mu (E.rightHalfPlaneHasInfiniteCluster r) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteClusterAtInfinity_measure_eq E mu hTI r

/--
[PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq_zero_or_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma rightHalfPlaneHasInfiniteCluster_measure_eq_zero_or_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : Real}
-- given
  (hErgodic : P.IsErgodic mu) :
-- imply
  mu (E.rightHalfPlaneHasInfiniteCluster r) = 0 ∨ mu (E.rightHalfPlaneHasInfiniteCluster r) = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq_zero_or_one E mu hErgodic r

/--
[PeriodicPlaneEmbedding.iUnion_orbitBox_setHitsInfiniteWithin_rightHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma iUnion_orbitBox_setHitsInfiniteWithin_rightHalfPlane_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : Real} :
-- imply
  (⋃ n : Nat, P.setHitsInfiniteWithin (E.rightHalfPlaneVertices r) ((P.orbitBox n : Set V) ∩ E.rightHalfPlaneVertices r)) = E.rightHalfPlaneHasInfiniteCluster r := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.iUnion_orbitBox_setHitsInfiniteWithin_rightHalfPlane E r

/--
[PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq_zero_of_orbitBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma rightHalfPlaneHasInfiniteCluster_measure_eq_zero_of_orbitBox_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {r : Real}
-- given
  (hzero : ∀ n : Nat, mu (P.setHitsInfiniteWithin (E.rightHalfPlaneVertices r) ((P.orbitBox n : Set V) ∩ E.rightHalfPlaneVertices r)) = 0) :
-- imply
  mu (E.rightHalfPlaneHasInfiniteCluster r) = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq_zero_of_orbitBox E mu r hzero

/--
[PeriodicPlaneEmbedding.rightHalfPlane_vertexEscape_measureReal_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma rightHalfPlane_vertexEscape_measureReal_tendsto_zero_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r : Real}
  {x : V}
-- given
  (hx : x ∈ E.rightHalfPlaneVertices r)
  (hnoInfinite : mu (E.rightHalfPlaneHasInfiniteCluster r) = 0) :
-- imply
  Tendsto (fun n => mu.real (P.clusterWithinSetEscape (E.rightHalfPlaneVertices r) x n)) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rightHalfPlane_vertexEscape_measureReal_tendsto_zero E mu r x hx hnoInfinite

/--
[PeriodicGraph.finiteSetEscapeWithin_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma finiteSetEscapeWithin_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {A : Set V}
  {L : Finset V}
  {n : Nat} :
-- imply
  MeasurableSet (P.finiteSetEscapeWithin A L n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.finiteSetEscapeWithin_measurableSet P A L n

/--
[PeriodicGraph.iInter_finiteSetEscapeWithin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma iInter_finiteSetEscapeWithin_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {A : Set V}
  {L : Finset V} :
-- imply
  (⋂ n : Nat, P.finiteSetEscapeWithin A L n) = P.setHitsInfiniteWithin A (L : Set V) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.iInter_finiteSetEscapeWithin P A L

/--
[PeriodicGraph.finiteSetEscapeWithin_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma finiteSetEscapeWithin_antitone_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {A : Set V}
  {L : Finset V} :
-- imply
  Antitone (P.finiteSetEscapeWithin A L) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.finiteSetEscapeWithin_antitone P A L

/--
[PeriodicGraph.finiteSetEscapeWithin_measureReal_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma finiteSetEscapeWithin_measureReal_tendsto_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {A : Set V}
  {L : Finset V} :
-- imply
  Tendsto (fun n => mu.real (P.finiteSetEscapeWithin A L n)) atTop (nhds (mu.real (P.setHitsInfiniteWithin A (L : Set V)))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.finiteSetEscapeWithin_measureReal_tendsto P mu A L

/--
[PeriodicPlaneEmbedding.rightHalfPlane_finiteSetEscape_measureReal_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma rightHalfPlane_finiteSetEscape_measureReal_tendsto_zero_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r : Real}
  {L : Finset V}
-- given
  (hL : (L : Set V) ⊆ E.rightHalfPlaneVertices r)
  (hnoInfinite : mu (E.rightHalfPlaneHasInfiniteCluster r) = 0) :
-- imply
  Tendsto (fun n => mu.real (P.finiteSetEscapeWithin (E.rightHalfPlaneVertices r) L n)) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rightHalfPlane_finiteSetEscape_measureReal_tendsto_zero E mu r L hL hnoInfinite

/--
[PeriodicPlaneEmbedding.rectSideConnectionEvent_subset_finiteSetEscapeWithin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma rectSideConnectionEvent_subset_finiteSetEscapeWithin_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {L : Finset V}
  {side A : Set V}
  {n : Nat}
-- given
  (hrect : E.rectVertices a b c d ⊆ A)
  (hside : side ⊆ (P.orbitBox n : Set V)ᶜ) :
-- imply
  E.rectSideConnectionEvent a b c d (L : Set V) side ⊆ P.finiteSetEscapeWithin A L n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectSideConnectionEvent_subset_finiteSetEscapeWithin E hrect hside

/--
[PeriodicPlaneEmbedding.rectSideConnection_measureReal_le_finiteSetEscapeWithin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean)
-/
@[path]
private lemma rectSideConnection_measureReal_le_finiteSetEscapeWithin_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {a b c d : Real}
  {L : Finset V}
  {side A : Set V}
  {n : Nat}
-- given
  (hrect : E.rectVertices a b c d ⊆ A)
  (hside : side ⊆ (P.orbitBox n : Set V)ᶜ) :
-- imply
  mu.real (E.rectSideConnectionEvent a b c d (L : Set V) side) ≤ mu.real (P.finiteSetEscapeWithin A L n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectSideConnection_measureReal_le_finiteSetEscapeWithin E mu hrect hside


-- created on 2026-10-23
