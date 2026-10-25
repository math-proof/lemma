import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.BKUniqueness2
open MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[enat_zero_or_one_of_not_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKUniqueness2.lean)
-/
@[path]
private lemma enat_zero_or_one_of_not_two_eq
  {d : ℕ}
  {k : ℕ∞}
-- given
  (h2 : ¬ (2 ≤ k)) :
-- imply
  k = 0 ∨ k = 1 := by
-- proof
  apply StatMech.Percolation.enat_zero_or_one_of_not_two h2

/--
[merge_event_null_of_construct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKUniqueness2.lean)
-/
@[path]
private lemma merge_event_null_of_construct_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hmergeConstruct : 0 < μ (atLeastTwoInfinite d) → μ (atLeastTwoInfinite d) = 0) :
-- imply
  μ (atLeastTwoInfinite d) = 0 := by
-- proof
  apply StatMech.Percolation.merge_event_null_of_construct μ hmergeConstruct

/--
[numInfiniteClusters_zero_or_one_of_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKUniqueness2.lean)
-/
@[path]
private lemma numInfiniteClusters_zero_or_one_of_const_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {k : ℕ∞}
-- given
  (hk : μ {ω | numInfiniteClusters d ω = k} = 1)
  (hmerge : μ (atLeastTwoInfinite d) = 0) :
-- imply
  μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1 := by
-- proof
  apply StatMech.Percolation.numInfiniteClusters_zero_or_one_of_const μ hk hmerge

/--
[numInfiniteClusters_zero_or_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKUniqueness2.lean)
-/
@[path]
private lemma numInfiniteClusters_zero_or_one_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hmerge : μ (atLeastTwoInfinite d) = 0) :
-- imply
  μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1 := by
-- proof
  apply StatMech.Percolation.numInfiniteClusters_zero_or_one μ herg hmerge

/--
[numInfiniteClusters_zero_or_one_of_mergeConstruct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKUniqueness2.lean)
-/
@[path]
private lemma numInfiniteClusters_zero_or_one_of_mergeConstruct_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hmergeConstruct : 0 < μ (atLeastTwoInfinite d) → μ (atLeastTwoInfinite d) = 0) :
-- imply
  μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1 := by
-- proof
  apply StatMech.Percolation.numInfiniteClusters_zero_or_one_of_mergeConstruct μ herg hmergeConstruct

/--
[burton_keane_uniqueness_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKUniqueness2.lean)
-/
@[path]
private lemma burton_keane_uniqueness_dichotomy_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {bdry : ℕ → ℕ}
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Filter.Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) Filter.atTop (nhds 0))
  (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → 0 < μ {ω | IsTrifurcation d ω 0})
  (hmerge : μ (atLeastTwoInfinite d) = 0) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 ∧ ∃ k : ℕ∞, (k = 0 ∨ k = 1) ∧ μ {ω | numInfiniteClusters d ω = k} = 1 := by
-- proof
  apply StatMech.Percolation.burton_keane_uniqueness_dichotomy μ herg bdry hbound hvol hdens htrif hmerge


-- created on 2026-10-23
