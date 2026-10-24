import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.BurtonKeaneErgodic
open MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[measurableSet_atLeastTwoInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneErgodic.lean)
-/
@[path]
private lemma measurableSet_atLeastTwoInfinite_eq
  {d : ℕ} :
-- imply
  MeasurableSet (atLeastTwoInfinite d) := by
-- proof
  apply StatMech.Percolation.measurableSet_atLeastTwoInfinite

/--
[atLeastTwoInfinite_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneErgodic.lean)
-/
@[path]
private lemma atLeastTwoInfinite_compl_eq
  {d : ℕ} :
-- imply
  (atLeastTwoInfinite d)ᶜ = {ω | numInfiniteClusters d ω ≤ 1} := by
-- proof
  apply StatMech.Percolation.atLeastTwoInfinite_compl

/--
[enat_le_one_of_not_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneErgodic.lean)
-/
@[path]
private lemma enat_le_one_of_not_two_eq
  {d : ℕ}
  {k : ℕ∞}
-- given
  (h2 : ¬ (2 ≤ k)) :
-- imply
  k ≤ 1 := by
-- proof
  apply StatMech.Percolation.enat_le_one_of_not_two h2

/--
[numInfiniteClusters_le_one_of_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneErgodic.lean)
-/
@[path]
private lemma numInfiniteClusters_le_one_of_const_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {k : ℕ∞}
-- given
  (hk : μ {ω | numInfiniteClusters d ω = k} = 1)
  (hmerge : μ (atLeastTwoInfinite d) = 0) :
-- imply
  μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.numInfiniteClusters_le_one_of_const μ hk hmerge

/--
[infiniteCluster_unique_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneErgodic.lean)
-/
@[path]
private lemma infiniteCluster_unique_ae_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hmerge : μ (atLeastTwoInfinite d) = 0) :
-- imply
  μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.infiniteCluster_unique_ae μ herg hmerge

/--
[burton_keane_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneErgodic.lean)
-/
@[path]
private lemma burton_keane_uniqueness_eq
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
  ∃ k : ℕ∞, k ≤ 1 ∧ μ {ω | numInfiniteClusters d ω = k} = 1 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.burton_keane_uniqueness μ herg bdry hbound hvol hdens htrif hmerge


-- created on 2026-10-23
