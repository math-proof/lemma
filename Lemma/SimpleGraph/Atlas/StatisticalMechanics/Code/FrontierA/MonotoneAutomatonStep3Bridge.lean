import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3Bridge.Part4
open MeasureTheory Set StatMech StatMech.FrontierA


/--
[one_le_numInfiniteClusters_siteToBond_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3Bridge.lean)
-/
@[path]
private lemma one_le_numInfiniteClusters_siteToBond_iff_eq
  {d : ℕ}
  {eta : ConfigSpace (Site d)} :
-- imply
  1 ≤ numInfiniteClusters d (siteToBond eta) ↔ ∃ x : Site d, (cluster d (siteToBond eta) x).Infinite := by
-- proof
  apply StatMech.FrontierA.one_le_numInfiniteClusters_siteToBond_iff eta

/--
[one_le_numInfiniteClusters_siteToBond_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3Bridge.lean)
-/
@[path]
private lemma one_le_numInfiniteClusters_siteToBond_mono_eq
  {d : ℕ}
  {eta eta' : ConfigSpace (Site d)}
-- given
  (h : eta ≤ eta')
  (hperco : 1 ≤ numInfiniteClusters d (siteToBond eta)) :
-- imply
  1 ≤ numInfiniteClusters d (siteToBond eta') := by
-- proof
  apply StatMech.FrontierA.one_le_numInfiniteClusters_siteToBond_mono h hperco

/--
[measurableSet_interpolatedSite_percolates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3Bridge.lean)
-/
@[path]
private lemma measurableSet_interpolatedSite_percolates_eq
  {d : ℕ}
  {T : MonotoneAutomaton d} :
-- imply
  MeasurableSet {q : FieldTriple d | 1 ≤ numInfiniteClusters d (siteToBond (interpolatedSite T q))} := by
-- proof
  apply StatMech.FrontierA.measurableSet_interpolatedSite_percolates T

/--
[measurableSet_lowOutput_percolates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3Bridge.lean)
-/
@[path]
private lemma measurableSet_lowOutput_percolates_eq
  {d : ℕ}
  {T : MonotoneAutomaton d} :
-- imply
  MeasurableSet {q : FieldTriple d | 1 ≤ numInfiniteClusters d (siteToBond (T q.1))} := by
-- proof
  apply StatMech.FrontierA.measurableSet_lowOutput_percolates T

/--
[interpolatedSite_percolates_of_lowOutput](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3Bridge.lean)
-/
@[path]
private lemma interpolatedSite_percolates_of_lowOutput_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (FieldTriple d)}
  [IsProbabilityMeasure mu]
-- given
  (hlow : mu {q | 1 ≤ numInfiniteClusters d (siteToBond (T q.1))} = 1) :
-- imply
  (interpolatedSiteLaw T mu) {eta | 1 ≤ numInfiniteClusters d (siteToBond eta)} = 1 := by
-- proof
  apply StatMech.FrontierA.interpolatedSite_percolates_of_lowOutput T mu hlow

/--
[interpolatedSite_cluster_count_ae_one_of_lowOutput](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3Bridge.lean)
-/
@[path]
private lemma interpolatedSite_cluster_count_ae_one_of_lowOutput_eq
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
  (hlow : mu {q | 1 ≤ numInfiniteClusters d (siteToBond (T q.1))} = 1) :
-- imply
  (interpolatedSiteLaw T mu) {eta | numInfiniteClusters d (siteToBond eta) = 1} = 1 := by
-- proof
  apply StatMech.FrontierA.interpolatedSite_cluster_count_ae_one_of_lowOutput T mu hd herg epsilon hepsilon hinsert hlow

/--
[measurableSet_pairHasFiniteNearestInfiniteHighCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3Bridge.lean)
-/
@[path]
private lemma measurableSet_pairHasFiniteNearestInfiniteHighCluster_eq
  {d : ℕ} :
-- imply
  MeasurableSet (pairHasFiniteNearestInfiniteHighCluster (d := d)) := by
-- proof
  apply StatMech.FrontierA.measurableSet_pairHasFiniteNearestInfiniteHighCluster

/--
[interpolatedHighPair_lowInfinite_nonempty_of_lowOutput](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3Bridge.lean)
-/
@[path]
private lemma interpolatedHighPair_lowInfinite_nonempty_of_lowOutput_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (FieldTriple d)}
  [IsProbabilityMeasure mu]
-- given
  (hlow : mu {q | 1 ≤ numInfiniteClusters d (siteToBond (T q.1))} = 1) :
-- imply
  (interpolatedHighPairLaw T mu) {omega | (pairLowInfiniteVertices omega).Nonempty} = 1 := by
-- proof
  apply StatMech.FrontierA.interpolatedHighPair_lowInfinite_nonempty_of_lowOutput T mu hlow

/--
[interpolatedHighPair_finiteNearestInfiniteHighCluster_measure_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3Bridge.lean)
-/
@[path]
private lemma interpolatedHighPair_finiteNearestInfiniteHighCluster_measure_zero_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (FieldTriple d)}
  [IsProbabilityMeasure mu]
-- given
  (hinv : IsTripleFieldTranslationInvariant mu)
  (hlow : mu {q | 1 ≤ numInfiniteClusters d (siteToBond (T q.1))} = 1) :
-- imply
  (interpolatedHighPairLaw T mu) (pairHasFiniteNearestInfiniteHighCluster (d := d)) = 0 := by
-- proof
  apply StatMech.FrontierA.interpolatedHighPair_finiteNearestInfiniteHighCluster_measure_zero T mu hinv hlow

/--
[measurableSet_highThresholdOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3Bridge.lean)
-/
@[path]
private lemma measurableSet_highThresholdOn_eq
  {d : ℕ}
  {t : NNReal}
  {S : Finset (Site d)} :
-- imply
  MeasurableSet (highThresholdOn (d := d) t S) := by
-- proof
  apply StatMech.FrontierA.measurableSet_highThresholdOn t S

/--
[highOutput_eq_true_of_highThresholdOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3Bridge.lean)
-/
@[path]
private lemma highOutput_eq_true_of_highThresholdOn_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {q : FieldTriple d}
  {S : Finset (Site d)}
  {x : Site d}
-- given
  (hq : q ∈ highThresholdOn T.threshold S)
  (hx : x ∈ S) :
-- imply
  T q.2.2 x = true := by
-- proof
  apply StatMech.FrontierA.highOutput_eq_true_of_highThresholdOn T q S hq x hx

/--
[highInsertionLowerBound_finset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3Bridge.lean)
-/
@[path]
private lemma highInsertionLowerBound_finset_eq
  {d : ℕ}
  {mu : Measure (FieldTriple d)}
  {t : NNReal}
  {S : Finset (Site d)}
  {A : Set (FieldTriple d)}
-- given
  (epsilon : ℝ≥0∞)
  (hinsert : HasHighInsertionLowerBound mu t epsilon)
  (hAmeas : MeasurableSet A)
  (hignore : TripleEventIgnoresHighOn S A) :
-- imply
  epsilon ^ S.card * mu A ≤ mu (A ∩ highThresholdOn t S) := by
-- proof
  apply StatMech.FrontierA.highInsertionLowerBound_finset mu t epsilon hinsert S A hAmeas hignore

/--
[measurableSet_pairHighCluster_meets_lowInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3Bridge.lean)
-/
@[path]
private lemma measurableSet_pairHighCluster_meets_lowInfinite_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  MeasurableSet {omega : PairSiteConfig d | (pairHighCluster omega x ∩ pairLowInfiniteVertices omega).Nonempty} := by
-- proof
  apply StatMech.FrontierA.measurableSet_pairHighCluster_meets_lowInfinite x

/--
[measurableSet_pairHighClusterAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3Bridge.lean)
-/
@[path]
private lemma measurableSet_pairHighClusterAbsorption_eq
  {d : ℕ} :
-- imply
  MeasurableSet {omega : PairSiteConfig d | PairHighClusterAbsorption omega} := by
-- proof
  apply StatMech.FrontierA.measurableSet_pairHighClusterAbsorption

/--
[high_cluster_count_le_one_of_low_unique_of_absorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3Bridge.lean)
-/
@[path]
private lemma high_cluster_count_le_one_of_low_unique_of_absorption_eq
  {d : ℕ}
  {omega : PairSiteConfig d}
-- given
  (hlow : numInfiniteClusters d (siteToBond (pairSiteLeft omega)) = 1)
  (hnested : pairSiteLeft omega ≤ pairSiteRight omega)
  (habsorb : PairHighClusterAbsorption omega) :
-- imply
  numInfiniteClusters d (siteToBond (pairSiteRight omega)) ≤ 1 := by
-- proof
  apply StatMech.FrontierA.high_cluster_count_le_one_of_low_unique_of_absorption omega hlow hnested habsorb

/--
[highOutput_cluster_count_ae_le_one_of_absorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3Bridge.lean)
-/
@[path]
private lemma highOutput_cluster_count_ae_le_one_of_absorption_eq
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
  (habsorb : ∀ᵐ q ∂mu, PairHighClusterAbsorption (interpolatedHighPair T q)) :
-- imply
  mu {q | numInfiniteClusters d (siteToBond (T q.2.2)) ≤ 1} = 1 := by
-- proof
  apply StatMech.FrontierA.highOutput_cluster_count_ae_le_one_of_absorption T mu hd herg epsilon hepsilon hinsert hmono hlow habsorb

/--
[highOutput_cluster_count_ae_one_of_absorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3Bridge.lean)
-/
@[path]
private lemma highOutput_cluster_count_ae_one_of_absorption_eq
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
  (habsorb : ∀ᵐ q ∂mu, PairHighClusterAbsorption (interpolatedHighPair T q)) :
-- imply
  mu {q | numInfiniteClusters d (siteToBond (T q.2.2)) = 1} = 1 := by
-- proof
  apply StatMech.FrontierA.highOutput_cluster_count_ae_one_of_absorption T mu hd herg epsilon hepsilon hinsert hmono hlow habsorb


-- created on 2026-10-23
