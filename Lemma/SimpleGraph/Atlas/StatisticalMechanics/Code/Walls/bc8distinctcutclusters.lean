import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc8distinctcutclusters.Part2
open Set SimpleGraph StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech StatMech.Walls


/--
[bc8_cutCluster_distinct_of_baseClusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8distinctcutclusters.lean)
-/
@[path]
private lemma bc8_cutCluster_distinct_of_baseClusters_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
-- given
  (hi1 : (cluster d ω x₁).Infinite)
  (hi2 : (cluster d ω x₂).Infinite)
  (hi3 : (cluster d ω x₃).Infinite)
  (hd12 : cluster d ω x₁ ≠ cluster d ω x₂)
  (hd13 : cluster d ω x₁ ≠ cluster d ω x₃)
  (hd23 : cluster d ω x₂ ≠ cluster d ω x₃) :
-- imply
  ∃ x₁' x₂' x₃' : Site d, x₁' ∈ cluster d ω x₁ ∧ x₂' ∈ cluster d ω x₂ ∧ x₃' ∈ cluster d ω x₃ ∧ (cluster d (removeSite 0 ω) x₁').Infinite ∧ (cluster d (removeSite 0 ω) x₂').Infinite ∧ (cluster d (removeSite 0 ω) x₃').Infinite ∧ cluster d (removeSite 0 ω) x₁' ≠ cluster d (removeSite 0 ω) x₂' ∧ cluster d (removeSite 0 ω) x₁' ≠ cluster d (removeSite 0 ω) x₃' ∧ cluster d (removeSite 0 ω) x₂' ≠ cluster d (removeSite 0 ω) x₃' := by
-- proof
  apply StatMech.Walls.bc8_cutCluster_distinct_of_baseClusters ω hi1 hi2 hi3 hd12 hd13 hd23

/--
[bc8_distinctCutClusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8distinctcutclusters.lean)
-/
@[path]
private lemma bc8_distinctCutClusters_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  bc8_DistinctCutClusters d n := by
-- proof
  apply StatMech.Walls.bc8_distinctCutClusters n

/--
[bc8_threeArmClusters_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8distinctcutclusters.lean)
-/
@[path]
private lemma bc8_threeArmClusters_distinct_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hω : ω ∈ threeMeetBox d n) :
-- imply
  ∃ x₁' x₂' x₃' : Site d, (cluster d (removeSite 0 ω) x₁').Infinite ∧ (cluster d (removeSite 0 ω) x₂').Infinite ∧ (cluster d (removeSite 0 ω) x₃').Infinite ∧ cluster d (removeSite 0 ω) x₁' ≠ cluster d (removeSite 0 ω) x₂' ∧ cluster d (removeSite 0 ω) x₁' ≠ cluster d (removeSite 0 ω) x₃' ∧ cluster d (removeSite 0 ω) x₂' ≠ cluster d (removeSite 0 ω) x₃' := by
-- proof
  apply StatMech.Walls.bc8_threeArmClusters_distinct n ω hω

/--
[bc8_distinctCutClusters_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8distinctcutclusters.lean)
-/
@[path]
private lemma bc8_distinctCutClusters_eq_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  bc8_DistinctCutClusters d n = bc7_DistinctWitnessClusters d n := by
-- proof
  apply StatMech.Walls.bc8_distinctCutClusters_eq n


-- created on 2026-10-23
