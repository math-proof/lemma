import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneUniqueness
open MeasureTheory Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.numInfiniteClusters_top_subset_threeDistinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneUniqueness.lean)
-/
@[path]
private lemma numInfiniteClusters_top_subset_threeDistinct_eq
  {V : Type}
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V} :
-- imply
  {omega | P.numInfiniteClusters omega = ⊤} ⊆ ⋃ x : Fin 3 → V, P.threeDistinctInfiniteEvent x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.numInfiniteClusters_top_subset_threeDistinct P

/--
[PeriodicGraph.exists_threeDistinctInfinite_pos_of_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneUniqueness.lean)
-/
@[path]
private lemma exists_threeDistinctInfinite_pos_of_top_eq
  {V : Type}
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
-- given
  (htop : 0 < mu {omega | P.numInfiniteClusters omega = ⊤}) :
-- imply
  ∃ x : Fin 3 → V, 0 < mu (P.threeDistinctInfiniteEvent x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.exists_threeDistinctInfinite_pos_of_top P mu htop

/--
[PeriodicGraph.threeDistinct_subset_pattern_trifurcations](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneUniqueness.lean)
-/
@[path]
private lemma threeDistinct_subset_pattern_trifurcations_eq
  {V : Type}
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {x : Fin 3 → V}
-- given
  (hconn : P.graph.Connected) :
-- imply
  P.threeDistinctInfiniteEvent x ⊆ ⋃ I : Finset (Sym2 V), ⋃ eta : ConfigSpace ↥I, ⋃ hub : V, setPattern I eta ⁻¹' {omega | P.IsTrifurcation omega hub} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.threeDistinct_subset_pattern_trifurcations P hconn x

/--
[PeriodicGraph.exists_trifurcation_pos_of_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneUniqueness.lean)
-/
@[path]
private lemma exists_trifurcation_pos_of_top_eq
  {V : Type}
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hconn : P.graph.Connected)
  (hpattern : ∀ (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I), mu.map (setPattern I eta) ≪ mu)
  (htop : 0 < mu {omega | P.numInfiniteClusters omega = ⊤}) :
-- imply
  ∃ hub : V, 0 < mu {omega | P.IsTrifurcation omega hub} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.exists_trifurcation_pos_of_top P hconn mu hpattern htop

/--
[PeriodicPlaneEmbedding.numInfiniteClusters_top_measure_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneUniqueness.lean)
-/
@[path]
private lemma numInfiniteClusters_top_measure_zero_eq
  {V : Type}
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hconn : P.graph.Connected)
  (hTI : P.IsTranslationInvariant mu)
  (hpattern : ∀ (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I), mu.map (setPattern I eta) ≪ mu) :
-- imply
  mu {omega | P.numInfiniteClusters omega = ⊤} = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.numInfiniteClusters_top_measure_zero E hconn mu hTI hpattern

/--
[PeriodicPlaneEmbedding.numInfiniteClusters_zero_or_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneUniqueness.lean)
-/
@[path]
private lemma numInfiniteClusters_zero_or_one_eq
  {V : Type}
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hconn : P.graph.Connected)
  (herg : P.IsErgodic mu)
  (hfe : HasFiniteEnergy mu)
  (hpattern : ∀ (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I), mu.map (setPattern I eta) ≪ mu) :
-- imply
  ∃ k : ℕ∞, mu {omega | P.numInfiniteClusters omega = k} = 1 ∧ (k = 0 ∨ k = 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.numInfiniteClusters_zero_or_one E hconn mu herg hfe hpattern

/--
[PeriodicPlaneEmbedding.freeBufferedInfiniteVolume_numInfiniteClusters_zero_or_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneUniqueness.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_numInfiniteClusters_zero_or_one_eq
  {V : Type}
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {E : PeriodicPlaneEmbedding P}
  {p q : Real}
-- given
  (hconn : P.graph.Connected)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  ∃ k : ℕ∞, (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | P.numInfiniteClusters omega = k} = 1 ∧ (k = 0 ∨ k = 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.freeBufferedInfiniteVolume_numInfiniteClusters_zero_or_one E hconn hp hp1 hq


-- created on 2026-10-23
