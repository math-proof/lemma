import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonAbsorptionReduction.Part3
open MeasureTheory Set StatMech StatMech.FrontierA


/--
[measurableSet_pairDisjointInfiniteHighAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonAbsorptionReduction.lean)
-/
@[path]
private lemma measurableSet_pairDisjointInfiniteHighAt_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  MeasurableSet (pairDisjointInfiniteHighAt x) := by
-- proof
  apply StatMech.FrontierA.measurableSet_pairDisjointInfiniteHighAt x

/--
[measurableSet_pairStep3CoreAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonAbsorptionReduction.lean)
-/
@[path]
private lemma measurableSet_pairStep3CoreAt_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  MeasurableSet (pairStep3CoreAt x) := by
-- proof
  apply StatMech.FrontierA.measurableSet_pairStep3CoreAt x

/--
[pairDisjointInfiniteHighAt_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonAbsorptionReduction.lean)
-/
@[path]
private lemma pairDisjointInfiniteHighAt_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {omega : PairSiteConfig d}
  {x : Site d} :
-- imply
  StatMech.ConfigSpace.shift g omega ∈ pairDisjointInfiniteHighAt (g • x) ↔ omega ∈ pairDisjointInfiniteHighAt x := by
-- proof
  apply StatMech.FrontierA.pairDisjointInfiniteHighAt_shift g omega x

/--
[pairDisjointInfiniteHighAt_measure_zero_of_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonAbsorptionReduction.lean)
-/
@[path]
private lemma pairDisjointInfiniteHighAt_measure_zero_of_origin_eq
  {d : ℕ}
  {nu : Measure (PairSiteConfig d)}
  [IsProbabilityMeasure nu]
  {x : Site d}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) nu)
  (hzero : nu (pairDisjointInfiniteHighAt (0 : Site d)) = 0) :
-- imply
  nu (pairDisjointInfiniteHighAt x) = 0 := by
-- proof
  apply StatMech.FrontierA.pairDisjointInfiniteHighAt_measure_zero_of_origin nu hinv hzero x

/--
[pairHasDisjointInfiniteHighCluster_eq_iUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonAbsorptionReduction.lean)
-/
@[path]
private lemma pairHasDisjointInfiniteHighCluster_eq_iUnion_eq
  {d : ℕ} :
-- imply
  pairHasDisjointInfiniteHighCluster (d := d) = ⋃ x : Site d, pairDisjointInfiniteHighAt x := by
-- proof
  apply StatMech.FrontierA.pairHasDisjointInfiniteHighCluster_eq_iUnion

/--
[measurableSet_pairHasDisjointInfiniteHighCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonAbsorptionReduction.lean)
-/
@[path]
private lemma measurableSet_pairHasDisjointInfiniteHighCluster_eq
  {d : ℕ} :
-- imply
  MeasurableSet (pairHasDisjointInfiniteHighCluster (d := d)) := by
-- proof
  apply StatMech.FrontierA.measurableSet_pairHasDisjointInfiniteHighCluster

/--
[pairHighClusterAbsorption_compl_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonAbsorptionReduction.lean)
-/
@[path]
private lemma pairHighClusterAbsorption_compl_eq_eq
  {d : ℕ} :
-- imply
  {omega : PairSiteConfig d | PairHighClusterAbsorption omega}ᶜ = pairHasDisjointInfiniteHighCluster := by
-- proof
  apply StatMech.FrontierA.pairHighClusterAbsorption_compl_eq

/--
[pairHighClusterAbsorption_ae_of_origin_disjoint_null](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonAbsorptionReduction.lean)
-/
@[path]
private lemma pairHighClusterAbsorption_ae_of_origin_disjoint_null_eq
  {d : ℕ}
  {nu : Measure (PairSiteConfig d)}
  [IsProbabilityMeasure nu]
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) nu)
  (hzero : nu (pairDisjointInfiniteHighAt (0 : Site d)) = 0) :
-- imply
  ∀ᵐ omega ∂nu, PairHighClusterAbsorption omega := by
-- proof
  apply StatMech.FrontierA.pairHighClusterAbsorption_ae_of_origin_disjoint_null nu hinv hzero

/--
[pairDisjointInfiniteHighAt_subset_finiteNearest_union_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonAbsorptionReduction.lean)
-/
@[path]
private lemma pairDisjointInfiniteHighAt_subset_finiteNearest_union_core_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  pairDisjointInfiniteHighAt x ⊆ pairHasFiniteNearestInfiniteHighCluster ∪ pairStep3CoreAt x := by
-- proof
  apply StatMech.FrontierA.pairDisjointInfiniteHighAt_subset_finiteNearest_union_core x

/--
[interpolatedHighPair_origin_disjoint_null_of_step3Core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonAbsorptionReduction.lean)
-/
@[path]
private lemma interpolatedHighPair_origin_disjoint_null_of_step3Core_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (FieldTriple d)}
  [IsProbabilityMeasure mu]
-- given
  (hinv : IsTripleFieldTranslationInvariant mu)
  (hlow : mu {q | 1 ≤ numInfiniteClusters d (siteToBond (T q.1))} = 1)
  (hcore : (interpolatedHighPairLaw T mu) (pairStep3CoreAt (0 : Site d)) = 0) :
-- imply
  (interpolatedHighPairLaw T mu) (pairDisjointInfiniteHighAt (0 : Site d)) = 0 := by
-- proof
  apply StatMech.FrontierA.interpolatedHighPair_origin_disjoint_null_of_step3Core T mu hinv hlow hcore

/--
[interpolatedHighPair_absorption_ae_of_step3Core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonAbsorptionReduction.lean)
-/
@[path]
private lemma interpolatedHighPair_absorption_ae_of_step3Core_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (FieldTriple d)}
  [IsProbabilityMeasure mu]
-- given
  (hinv : IsTripleFieldTranslationInvariant mu)
  (hlow : mu {q | 1 ≤ numInfiniteClusters d (siteToBond (T q.1))} = 1)
  (hcore : (interpolatedHighPairLaw T mu) (pairStep3CoreAt (0 : Site d)) = 0) :
-- imply
  ∀ᵐ q ∂mu, PairHighClusterAbsorption (interpolatedHighPair T q) := by
-- proof
  apply StatMech.FrontierA.interpolatedHighPair_absorption_ae_of_step3Core T mu hinv hlow hcore

/--
[highOutput_cluster_count_ae_le_one_of_step3Core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonAbsorptionReduction.lean)
-/
@[path]
private lemma highOutput_cluster_count_ae_le_one_of_step3Core_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (FieldTriple d)}
  [IsProbabilityMeasure mu]
-- given
  (hd : 1 ≤ d)
  (herg : IsTripleFieldErgodic mu)
  (epsilon : ℝ≥0∞)
  (hepsilon : epsilon ≠ 0)
  (hinsert : HasMiddleInsertionLowerBound mu T.threshold epsilon)
  (hmono : ∀ᵐ q ∂mu, IsMonotoneFieldTriple q)
  (hlow : mu {q | 1 ≤ numInfiniteClusters d (siteToBond (T q.1))} = 1)
  (hcore : (interpolatedHighPairLaw T mu) (pairStep3CoreAt (0 : Site d)) = 0) :
-- imply
  mu {q | numInfiniteClusters d (siteToBond (T q.2.2)) ≤ 1} = 1 := by
-- proof
  apply StatMech.FrontierA.highOutput_cluster_count_ae_le_one_of_step3Core T mu hd herg epsilon hepsilon hinsert hmono hlow hcore


-- created on 2026-10-23
