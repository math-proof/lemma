import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMergeGeom
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[twoMeetBox_subset_mergeWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMergeGeom.lean)
-/
@[path]
private lemma twoMeetBox_subset_mergeWitness_eq
  {d : ℕ}
  {n : ℕ}
  {k : ℕ∞} :
-- imply
  twoMeetBox d n k ⊆ MergeWitness d (boxEdges d n) k := by
-- proof
  apply StatMech.Percolation.twoMeetBox_subset_mergeWitness n k

/--
[iEqLevel_subset_iUnion_twoMeetBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMergeGeom.lean)
-/
@[path]
private lemma iEqLevel_subset_iUnion_twoMeetBox_eq
  {d : ℕ}
  {k : ℕ∞}
-- given
  (hk2 : 2 ≤ k) :
-- imply
  {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = k} ⊆ ⋃ n, twoMeetBox d n k := by
-- proof
  apply StatMech.Percolation.iEqLevel_subset_iUnion_twoMeetBox hk2

/--
[exists_twoMeetBox_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMergeGeom.lean)
-/
@[path]
private lemma exists_twoMeetBox_pos_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {k : ℕ∞}
-- given
  (hk2 : 2 ≤ k)
  (hk : μ {ω | numInfiniteClusters d ω = k} = 1) :
-- imply
  ∃ n : ℕ, 0 < μ (twoMeetBox d n k) := by
-- proof
  apply StatMech.Percolation.exists_twoMeetBox_pos μ hk2 hk

/--
[hmergeGeom_discharged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMergeGeom.lean)
-/
@[path]
private lemma hmergeGeom_discharged_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {k : ℕ∞}
-- given
  (hk2 : 2 ≤ k)
  (_hktop : k ≠ ⊤)
  (hk : μ {ω | numInfiniteClusters d ω = k} = 1) :
-- imply
  ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k) := by
-- proof
  apply StatMech.Percolation.hmergeGeom_discharged μ k hk2 _hktop hk

/--
[burton_keane_uniqueness_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMergeGeom.lean)
-/
@[path]
private lemma burton_keane_uniqueness_full_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {bdry : ℕ → ℕ}
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Filter.Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) Filter.atTop (nhds 0))
  (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → 0 < μ {ω | IsTrifurcation d ω 0}) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.burton_keane_uniqueness_full μ herg hfe bdry hbound hvol hdens htrif


-- created on 2026-10-23
