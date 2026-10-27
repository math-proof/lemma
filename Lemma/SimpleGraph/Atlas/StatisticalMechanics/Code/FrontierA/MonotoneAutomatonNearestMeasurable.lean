import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonNearestMeasurable.Part2
open MeasureTheory Set StatMech StatMech.FrontierA


/--
[measurableSet_pairHighConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestMeasurable.lean)
-/
@[path]
private lemma measurableSet_pairHighConnected_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  MeasurableSet {omega : PairSiteConfig d | y ∈ pairHighCluster omega x} := by
-- proof
  apply StatMech.FrontierA.measurableSet_pairHighConnected x y

/--
[measurableSet_pairLowInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestMeasurable.lean)
-/
@[path]
private lemma measurableSet_pairLowInfinite_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  MeasurableSet {omega : PairSiteConfig d | x ∈ pairLowInfiniteVertices omega} := by
-- proof
  apply StatMech.FrontierA.measurableSet_pairLowInfinite x

/--
[measurableSet_pairHighInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestMeasurable.lean)
-/
@[path]
private lemma measurableSet_pairHighInfinite_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  MeasurableSet {omega : PairSiteConfig d | (pairHighCluster omega x).Infinite} := by
-- proof
  apply StatMech.FrontierA.measurableSet_pairHighInfinite x

/--
[measurableSet_pairNearestComparisonEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestMeasurable.lean)
-/
@[path]
private lemma measurableSet_pairNearestComparisonEvent_eq
  {d : ℕ}
  {x y z x' y' : Site d} :
-- imply
  MeasurableSet (pairNearestComparisonEvent x y z x' y') := by
-- proof
  apply StatMech.FrontierA.measurableSet_pairNearestComparisonEvent x y z x' y'

/--
[measurableSet_pairNearestHighSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestMeasurable.lean)
-/
@[path]
private lemma measurableSet_pairNearestHighSet_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  MeasurableSet {omega : PairSiteConfig d | y ∈ pairNearestHighSet omega x} := by
-- proof
  apply StatMech.FrontierA.measurableSet_pairNearestHighSet x y

/--
[measurable_encard_setOf_countable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestMeasurable.lean)
-/
@[path]
private lemma measurable_encard_setOf_countable_eq
  {d : ℕ}
  [MeasurableSpace Omega]
  [Countable alpha]
-- given
  (p : Omega → alpha → Prop)
  (hp : ∀ a, Measurable (fun omega => p omega a)) :
-- imply
  Measurable (fun omega => Set.encard {a | p omega a}) := by
-- proof
  apply StatMech.FrontierA.measurable_encard_setOf_countable p hp

/--
[measurable_pairNearestHighSet_encard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestMeasurable.lean)
-/
@[path]
private lemma measurable_pairNearestHighSet_encard_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  Measurable (fun omega : PairSiteConfig d => (pairNearestHighSet omega x).encard) := by
-- proof
  apply StatMech.FrontierA.measurable_pairNearestHighSet_encard x

/--
[measurable_pairNearestHighSet_ncard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestMeasurable.lean)
-/
@[path]
private lemma measurable_pairNearestHighSet_ncard_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  Measurable (fun omega : PairSiteConfig d => (pairNearestHighSet omega x).ncard) := by
-- proof
  apply StatMech.FrontierA.measurable_pairNearestHighSet_ncard x

/--
[measurableSet_pairNearestHighSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestMeasurable.lean)
-/
@[path]
private lemma measurableSet_pairNearestHighSet_finite_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  MeasurableSet {omega : PairSiteConfig d | (pairNearestHighSet omega x).Finite} := by
-- proof
  apply StatMech.FrontierA.measurableSet_pairNearestHighSet_finite x

/--
[measurableSet_pairNearestHighFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestMeasurable.lean)
-/
@[path]
private lemma measurableSet_pairNearestHighFinset_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  MeasurableSet {omega : PairSiteConfig d | y ∈ pairNearestHighFinset omega x} := by
-- proof
  apply StatMech.FrontierA.measurableSet_pairNearestHighFinset x y

/--
[measurable_pairNearestHighFinset_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestMeasurable.lean)
-/
@[path]
private lemma measurable_pairNearestHighFinset_card_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  Measurable (fun omega : PairSiteConfig d => (pairNearestHighFinset omega x).card) := by
-- proof
  apply StatMech.FrontierA.measurable_pairNearestHighFinset_card x

/--
[measurable_pairNearestTransport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestMeasurable.lean)
-/
@[path]
private lemma measurable_pairNearestTransport_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  Measurable (pairNearestTransport x y : PairSiteConfig d → ℝ≥0∞) := by
-- proof
  apply StatMech.FrontierA.measurable_pairNearestTransport x y


-- created on 2026-10-23
