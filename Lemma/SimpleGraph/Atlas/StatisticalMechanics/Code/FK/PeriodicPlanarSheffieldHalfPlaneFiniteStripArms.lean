import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneFiniteStripArms.Part2
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.infiniteSetConnectionWithin_mono_region](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneFiniteStripArms.lean)
-/
@[path]
private lemma infiniteSetConnectionWithin_mono_region_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {A B : Set V}
  {S T : Set V}
-- given
  (hAB : A ⊆ B) :
-- imply
  P.infiniteSetConnectionWithin A S T ⊆ P.infiniteSetConnectionWithin B S T := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.infiniteSetConnectionWithin_mono_region P hAB S T

/--
[PeriodicPlaneEmbedding.finiteStripJoinedBoundaryArmEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneFiniteStripArms.lean)
-/
@[path]
private lemma finiteStripJoinedBoundaryArmEvent_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r c d : Real}
  {n : Nat}
  {L R : Finset V} :
-- imply
  MeasurableSet (E.finiteStripJoinedBoundaryArmEvent r c d n L R) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteStripJoinedBoundaryArmEvent_measurableSet E r c d n L R

/--
[PeriodicPlaneEmbedding.finiteStripJoinedBoundaryArmEvent_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneFiniteStripArms.lean)
-/
@[path]
private lemma finiteStripJoinedBoundaryArmEvent_mono_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r c d : Real}
  {L R : Finset V} :
-- imply
  Monotone (fun n => E.finiteStripJoinedBoundaryArmEvent r c d n L R) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteStripJoinedBoundaryArmEvent_mono E r c d L R

/--
[PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_subset_iUnion_finiteStrip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneFiniteStripArms.lean)
-/
@[path]
private lemma finiteJoinedBoundaryArmEvent_subset_iUnion_finiteStrip_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r c d : Real}
  {n₀ : Nat}
  {L R : Finset V} :
-- imply
  E.finiteJoinedBoundaryArmEvent r c d n₀ L R ⊆ ⋃ n : Nat, E.finiteStripJoinedBoundaryArmEvent r c d n L R := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_subset_iUnion_finiteStrip E r c d n₀ L R

/--
[PeriodicPlaneEmbedding.finiteStripJoinedBoundaryArmEvent_measureReal_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneFiniteStripArms.lean)
-/
@[path]
private lemma finiteStripJoinedBoundaryArmEvent_measureReal_tendsto_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {r c d : Real}
  {L R : Finset V} :
-- imply
  Tendsto (fun n => mu.real (E.finiteStripJoinedBoundaryArmEvent r c d n L R)) atTop (nhds (mu.real (⋃ n : Nat, E.finiteStripJoinedBoundaryArmEvent r c d n L R))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteStripJoinedBoundaryArmEvent_measureReal_tendsto E mu r c d L R

/--
[PeriodicPlaneEmbedding.exists_finiteStripJoinedBoundaryArmEvent_measureReal_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneFiniteStripArms.lean)
-/
@[path]
private lemma exists_finiteStripJoinedBoundaryArmEvent_measureReal_gt_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r c d : Real}
  {n₀ : Nat}
  {L R : Finset V}
  {epsilon : Real}
-- given
  (hprob : 1 - epsilon < mu.real (E.finiteJoinedBoundaryArmEvent r c d n₀ L R)) :
-- imply
  ∃ n : Nat, 1 - epsilon < mu.real (E.finiteStripJoinedBoundaryArmEvent r c d n L R) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_finiteStripJoinedBoundaryArmEvent_measureReal_gt E mu r c d n₀ L R hprob

/--
[PeriodicPlaneEmbedding.exists_highProbability_finiteJoinedBoundaryArmEvent_with_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneFiniteStripArms.lean)
-/
@[path]
private lemma exists_highProbability_finiteJoinedBoundaryArmEvent_with_separation_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r R : Real}
  {s : Real}
  {t : Int}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hrR : r ≤ R)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ L U : Finset V, ∃ n : Nat, (L : Set V) ⊆ E.rightHalfPlaneVertices R ∧ 1 - epsilon < mu.real (E.finiteJoinedBoundaryArmEvent r s (s + t) n L U) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_highProbability_finiteJoinedBoundaryArmEvent_with_separation E mu hFKG hTI hunique hrR s t hepsilon

/--
[PeriodicPlaneEmbedding.exists_highProbability_finiteStripJoinedBoundaryArmEvent_with_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneFiniteStripArms.lean)
-/
@[path]
private lemma exists_highProbability_finiteStripJoinedBoundaryArmEvent_with_separation_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r R : Real}
  {s : Real}
  {t : Int}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hrR : r ≤ R)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ L U : Finset V, ∃ n : Nat, (L : Set V) ⊆ E.rightHalfPlaneVertices R ∧ 1 - epsilon < mu.real (E.finiteStripJoinedBoundaryArmEvent r s (s + t) n L U) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_highProbability_finiteStripJoinedBoundaryArmEvent_with_separation E mu hFKG hTI hunique hrR s t hepsilon

/--
[PeriodicPlaneEmbedding.exists_rowwise_finiteStripJoinedBoundaryArms_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneFiniteStripArms.lean)
-/
@[path]
private lemma exists_rowwise_finiteStripJoinedBoundaryArms_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r R s : Nat → Real}
  {t : Nat → Int}
  {minimumWidth : Nat → Nat}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hrR : ∀ n, r n ≤ R n) :
-- imply
  ∃ lower upper : Nat → Finset V, ∃ width : Nat → Nat, (∀ n, minimumWidth n ≤ width n) ∧ (∀ n, (lower n : Set V) ⊆ E.rightHalfPlaneVertices (R n)) ∧ Tendsto (fun n ↦ mu.real (E.finiteStripJoinedBoundaryArmEvent (r n) (s n) (s n + t n) (width n) (lower n) (upper n))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_rowwise_finiteStripJoinedBoundaryArms_tendsto_one E mu hFKG hTI hunique r R s t hrR minimumWidth

/--
[PeriodicPlaneEmbedding.finiteStripJoinedBoundaryArmEvent_openWalks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneFiniteStripArms.lean)
-/
@[path]
private lemma finiteStripJoinedBoundaryArmEvent_openWalks_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {omega : ConfigSpace (Sym2 V)}
  {r c d : Real}
  {n : Nat}
  {L R : Finset V}
-- given
  (h : omega ∈ E.finiteStripJoinedBoundaryArmEvent r c d n L R) :
-- imply
  ∃ b ∈ E.lowerBoundaryRayVertices r c, ∃ u ∈ E.upperBoundaryRayVertices r d, ∃ j : V, ∃ lower : (P.openSubgraph omega).Walk b j, ∃ upper : (P.openSubgraph omega).Walk u j, j ∈ L ∧ (∀ v ∈ lower.support, v ∈ E.rightHalfPlaneStripVertices r n) ∧ ∀ v ∈ upper.support, v ∈ E.rightHalfPlaneStripVertices r n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteStripJoinedBoundaryArmEvent_openWalks E h

/--
[PeriodicPlaneEmbedding.finiteStripJoinedBoundaryArmEvent_graphWalks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneFiniteStripArms.lean)
-/
@[path]
private lemma finiteStripJoinedBoundaryArmEvent_graphWalks_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {omega : ConfigSpace (Sym2 V)}
  {r c d : Real}
  {n : Nat}
  {L R : Finset V}
-- given
  (h : omega ∈ E.finiteStripJoinedBoundaryArmEvent r c d n L R) :
-- imply
  ∃ b ∈ E.lowerBoundaryRayVertices r c, ∃ u ∈ E.upperBoundaryRayVertices r d, ∃ j : V, ∃ lower : P.graph.Walk b j, ∃ upper : P.graph.Walk u j, j ∈ L ∧ (∀ {x y : V}, s(x, y) ∈ lower.edges → omega s(x, y) = true) ∧ (∀ {x y : V}, s(x, y) ∈ upper.edges → omega s(x, y) = true) ∧ (∀ v ∈ lower.support, v ∈ E.rightHalfPlaneStripVertices r n) ∧ ∀ v ∈ upper.support, v ∈ E.rightHalfPlaneStripVertices r n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteStripJoinedBoundaryArmEvent_graphWalks E h

/--
[PeriodicPlaneEmbedding.walkArc_horizontal_strict_bounds_of_strip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneFiniteStripArms.lean)
-/
@[path]
private lemma walkArc_horizontal_strict_bounds_of_strip_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {B r : Real}
  {n : Nat}
  {x y : V}
  {p : P.graph.Walk x y}
-- given
  (hB : ∀ {u v : V} (huv : P.graph.Adj u v) (t) (i : Fin 2), |E.coordinates (E.edgeArc huv t - E.vertex u) i| ≤ B)
  (hB0 : 0 ≤ B)
  (hp : ∀ v ∈ p.support, v ∈ E.rightHalfPlaneStripVertices r n) :
-- imply
  ∀ t : unitInterval, r - B - 1 < E.coordinates (E.walkArc p t) 0 ∧ E.coordinates (E.walkArc p t) 0 < r + n + B + 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.walkArc_horizontal_strict_bounds_of_strip E hB hB0 p hp

/--
[PeriodicPlaneEmbedding.finiteStripJoinedBoundaryArmEvent_barrierGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneFiniteStripArms.lean)
-/
@[path]
private lemma finiteStripJoinedBoundaryArmEvent_barrierGeometry_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {omega : ConfigSpace (Sym2 V)}
  {B r c d : Real}
  {n : Nat}
  {L R : Finset V}
-- given
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (hB0 : 0 ≤ B)
  (hcd : c < d)
  (hLdeep : (L : Set V) ⊆ E.rightHalfPlaneVertices (r + B))
  (h : omega ∈ E.finiteStripJoinedBoundaryArmEvent r c d n L R) :
-- imply
  let a := r - B - 1 let b := r + n + B + 1 let C := (2 * c + d) / 3 let D := (c + 2 * d) / 3 a < b ∧ C < D ∧ ∃ xl xu xj : V, ∃ lower : P.graph.Walk xl xj, ∃ upper : P.graph.Walk xu xj, ¬ lower.Nil ∧ ¬ upper.Nil ∧ (∀ {x y : V}, s(x, y) ∈ lower.edges → omega s(x, y) = true) ∧ (∀ {x y : V}, s(x, y) ∈ upper.edges → omega s(x, y) = true) ∧ E.vertexCoord xl 1 < C ∧ D < E.vertexCoord xu 1 ∧ (∀ t : unitInterval, a < E.coordinates (E.walkArc lower t) 0 ∧ E.coordinates (E.walkArc lower t) 0 < b) ∧ ∀ t : unitInterval, a < E.coordinates (E.walkArc upper t) 0 ∧ E.coordinates (E.walkArc upper t) 0 < b := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteStripJoinedBoundaryArmEvent_barrierGeometry E hB hB0 hcd hLdeep h


-- created on 2026-10-23
