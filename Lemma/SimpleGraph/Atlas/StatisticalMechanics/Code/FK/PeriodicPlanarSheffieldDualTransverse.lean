import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDualTransverse.Part3
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.abs_vertexCoord_le_orbitBoxCoordinateBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTransverse.lean)
-/
@[path]
private lemma abs_vertexCoord_le_orbitBoxCoordinateBound_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {n : Nat}
  {v : V}
  {i : Fin 2}
-- given
  (hv : v ∈ P.orbitBox n) :
-- imply
  |E.vertexCoord v i| ≤ E.orbitBoxCoordinateBound n i := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.abs_vertexCoord_le_orbitBoxCoordinateBound E hv i

/--
[PeriodicPlaneEmbedding.walkArc_abs_coord_le_of_support_orbitBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTransverse.lean)
-/
@[path]
private lemma walkArc_abs_coord_le_of_support_orbitBox_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {B : Real}
  {n : Nat}
  {x y : V}
  {q : P.graph.Walk x y}
-- given
  (hB0 : 0 ≤ B)
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (hq : ∀ v ∈ q.support, v ∈ P.orbitBox n) :
-- imply
  ∀ (t : unitInterval) (i : Fin 2), |E.coordinates (E.walkArc q t) i| ≤ E.orbitBoxCoordinateBound n i + B := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.walkArc_abs_coord_le_of_support_orbitBox E hB0 hB q hq

/--
[PeriodicGraph.finiteSetHitsInfinite_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTransverse.lean)
-/
@[path]
private lemma finiteSetHitsInfinite_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {L : Finset V} :
-- imply
  MeasurableSet (P.finiteSetHitsInfinite L) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.finiteSetHitsInfinite_measurableSet P L

/--
[PeriodicGraph.finiteSetHitsInfinite_image_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTransverse.lean)
-/
@[path]
private lemma finiteSetHitsInfinite_image_shift_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {n : Nat} :
-- imply
  P.finiteSetHitsInfinite ((P.orbitBox n).image (P.shift z)) = P.translatedOrbitBoxHitsInfinite z n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.finiteSetHitsInfinite_image_shift P z n

/--
[PeriodicGraph.pairMergeErrorUnion_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTransverse.lean)
-/
@[path]
private lemma pairMergeErrorUnion_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {L R : Finset V}
  {N : Nat} :
-- imply
  MeasurableSet (P.pairMergeErrorUnion L R N) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.pairMergeErrorUnion_measurableSet P L R N

/--
[PeriodicGraph.finiteInfinitePairConnectionEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTransverse.lean)
-/
@[path]
private lemma finiteInfinitePairConnectionEvent_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {L R : Finset V}
  {N : Nat} :
-- imply
  MeasurableSet (P.finiteInfinitePairConnectionEvent L R N) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.finiteInfinitePairConnectionEvent_measurableSet P L R N

/--
[PeriodicGraph.finiteInfinitePairConnectionEvent_witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTransverse.lean)
-/
@[path]
private lemma finiteInfinitePairConnectionEvent_witnesses_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {L R : Finset V}
  {N : Nat}
-- given
  (h : omega ∈ P.finiteInfinitePairConnectionEvent L R N) :
-- imply
  ∃ x ∈ L, (P.cluster omega x).Infinite ∧ ∃ y ∈ R, (P.cluster omega y).Infinite ∧ omega ∈ P.connectedWithinOrbit x y N := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.finiteInfinitePairConnectionEvent_witnesses P h

/--
[PeriodicGraph.finiteInfinitePairConnectionEvent_graphWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTransverse.lean)
-/
@[path]
private lemma finiteInfinitePairConnectionEvent_graphWalk_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {L R : Finset V}
  {N : Nat}
-- given
  (h : omega ∈ P.finiteInfinitePairConnectionEvent L R N) :
-- imply
  ∃ x ∈ L, ∃ y ∈ R, ∃ q : P.graph.Walk x y, (∀ v ∈ q.support, v ∈ P.orbitBox (P.bufferedRadius N)) ∧ ∀ {u v : V}, s(u, v) ∈ q.edges → omega s(u, v) = true := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.finiteInfinitePairConnectionEvent_graphWalk P h

/--
[PeriodicGraph.finiteInfinitePairConnectionEvent_graphWalk_coordBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTransverse.lean)
-/
@[path]
private lemma finiteInfinitePairConnectionEvent_graphWalk_coordBounds_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {E : PeriodicPlaneEmbedding P}
  {B : Real}
  {omega : ConfigSpace (Sym2 V)}
  {L R : Finset V}
  {N : Nat}
-- given
  (hB0 : 0 ≤ B)
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (h : omega ∈ P.finiteInfinitePairConnectionEvent L R N) :
-- imply
  ∃ x ∈ L, ∃ y ∈ R, ∃ q : P.graph.Walk x y, (∀ {u v : V}, s(u, v) ∈ q.edges → omega s(u, v) = true) ∧ ∀ (t : unitInterval) (i : Fin 2), |E.coordinates (E.walkArc q t) i| ≤ E.orbitBoxCoordinateBound (P.bufferedRadius N) i + B := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.finiteInfinitePairConnectionEvent_graphWalk_coordBounds P E hB0 hB h

/--
[PeriodicGraph.finiteInfinitePairConnectionEvent_measureReal_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTransverse.lean)
-/
@[path]
private lemma finiteInfinitePairConnectionEvent_measureReal_ge_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {L R : Finset V}
  {N : Nat} :
-- imply
  mu.real (P.finiteSetHitsInfinite L) + mu.real (P.finiteSetHitsInfinite R) - mu.real (P.pairMergeErrorUnion L R N) - 1 ≤ mu.real (P.finiteInfinitePairConnectionEvent L R N) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.finiteInfinitePairConnectionEvent_measureReal_ge P mu L R N

/--
[PeriodicGraph.exists_highProbability_translatedBoxPairConnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTransverse.lean)
-/
@[path]
private lemma exists_highProbability_translatedBoxPairConnection_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {zL zR : Site 2}
  {epsilon : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ n N : Nat, 1 - epsilon < mu.real (P.finiteInfinitePairConnectionEvent ((P.orbitBox n).image (P.shift zL)) ((P.orbitBox n).image (P.shift zR)) N) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.exists_highProbability_translatedBoxPairConnection P mu hTI hunique zL zR hepsilon

/--
[PeriodicGraph.exists_uniformRadius_highProbability_translatedBoxPairConnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTransverse.lean)
-/
@[path]
private lemma exists_uniformRadius_highProbability_translatedBoxPairConnection_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {epsilon : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ n : Nat, ∀ zL zR : Site 2, ∃ N : Nat, 1 - epsilon < mu.real (P.finiteInfinitePairConnectionEvent ((P.orbitBox n).image (P.shift zL)) ((P.orbitBox n).image (P.shift zR)) N) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.exists_uniformRadius_highProbability_translatedBoxPairConnection P mu hTI hunique hepsilon


-- created on 2026-10-23
