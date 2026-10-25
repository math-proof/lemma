import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonNearestConclusion.Part2
open MeasureTheory Set StatMech StatMech.FrontierA


/--
[measurableSet_pairLowInfiniteVertices_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestConclusion.lean)
-/
@[path]
private lemma measurableSet_pairLowInfiniteVertices_nonempty_eq
  {d : ℕ} :
-- imply
  MeasurableSet {omega : PairSiteConfig d | (pairLowInfiniteVertices omega).Nonempty} := by
-- proof
  apply StatMech.FrontierA.measurableSet_pairLowInfiniteVertices_nonempty

/--
[measurableSet_pairFiniteNearestAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestConclusion.lean)
-/
@[path]
private lemma measurableSet_pairFiniteNearestAt_eq
  {d : ℕ}
  {y : Site d} :
-- imply
  MeasurableSet (pairFiniteNearestAt y) := by
-- proof
  apply StatMech.FrontierA.measurableSet_pairFiniteNearestAt y

/--
[pairFiniteNearestAt_origin_measure_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestConclusion.lean)
-/
@[path]
private lemma pairFiniteNearestAt_origin_measure_zero_eq
  {d : ℕ}
  {mu : Measure (PairSiteConfig d)}
  [IsProbabilityMeasure mu]
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu) :
-- imply
  mu (pairFiniteNearestAt (0 : Site d)) = 0 := by
-- proof
  apply StatMech.FrontierA.pairFiniteNearestAt_origin_measure_zero mu hinv

/--
[pairFiniteNearestAt_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestConclusion.lean)
-/
@[path]
private lemma pairFiniteNearestAt_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {omega : PairSiteConfig d}
  {x : Site d} :
-- imply
  StatMech.ConfigSpace.shift g omega ∈ pairFiniteNearestAt (g • x) ↔ omega ∈ pairFiniteNearestAt x := by
-- proof
  apply StatMech.FrontierA.pairFiniteNearestAt_shift g omega x

/--
[pairFiniteNearestAt_measure_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestConclusion.lean)
-/
@[path]
private lemma pairFiniteNearestAt_measure_zero_eq
  {d : ℕ}
  {mu : Measure (PairSiteConfig d)}
  [IsProbabilityMeasure mu]
  {y : Site d}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu) :
-- imply
  mu (pairFiniteNearestAt y) = 0 := by
-- proof
  apply StatMech.FrontierA.pairFiniteNearestAt_measure_zero mu hinv y

/--
[pairHasFiniteNearestHighCluster_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestConclusion.lean)
-/
@[path]
private lemma pairHasFiniteNearestHighCluster_subset_eq
  {d : ℕ} :
-- imply
  pairHasFiniteNearestHighCluster (d := d) ⊆ ⋃ y : Site d, pairFiniteNearestAt y := by
-- proof
  apply StatMech.FrontierA.pairHasFiniteNearestHighCluster_subset

/--
[pairHasFiniteNearestHighCluster_measure_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestConclusion.lean)
-/
@[path]
private lemma pairHasFiniteNearestHighCluster_measure_zero_eq
  {d : ℕ}
  {mu : Measure (PairSiteConfig d)}
  [IsProbabilityMeasure mu]
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu) :
-- imply
  mu (pairHasFiniteNearestHighCluster (d := d)) = 0 := by
-- proof
  apply StatMech.FrontierA.pairHasFiniteNearestHighCluster_measure_zero mu hinv

/--
[interpolatedHighPair_no_finite_nearest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestConclusion.lean)
-/
@[path]
private lemma interpolatedHighPair_no_finite_nearest_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (FieldTriple d)}
  [IsProbabilityMeasure mu]
-- given
  (hinv : IsTripleFieldTranslationInvariant mu) :
-- imply
  (interpolatedHighPairLaw T mu) (pairHasFiniteNearestHighCluster (d := d)) = 0 := by
-- proof
  apply StatMech.FrontierA.interpolatedHighPair_no_finite_nearest T mu hinv


-- created on 2026-10-23
