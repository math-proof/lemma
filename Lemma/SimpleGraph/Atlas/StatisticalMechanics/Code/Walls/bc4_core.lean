import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc4_core
open Set SimpleGraph StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech StatMech.Walls


/--
[bc4c_origin_neighbour_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_core.lean)
-/
@[path]
private lemma bc4c_origin_neighbour_of_connected_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {y : Site d}
-- given
  (hy0 : y ≠ 0)
  (hconn : Connected d ω 0 y) :
-- imply
  ∃ n, (openSubgraph d ω).Adj 0 n ∧ ∃ r : (openSubgraph d ω).Walk n y, (0 : Site d) ∉ r.support := by
-- proof
  apply StatMech.Walls.bc4c_origin_neighbour_of_connected ω hy0 hconn

/--
[bc4c_mem_neighbour_cutCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_core.lean)
-/
@[path]
private lemma bc4c_mem_neighbour_cutCluster_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {y : Site d}
-- given
  (hy0 : y ≠ 0)
  (hconn : Connected d ω 0 y) :
-- imply
  ∃ n, (openSubgraph d ω).Adj 0 n ∧ y ∈ cluster d (removeSite 0 ω) n := by
-- proof
  apply StatMech.Walls.bc4c_mem_neighbour_cutCluster ω hy0 hconn

/--
[bc4c_punctured_cluster_subset_neighbour_cutClusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_core.lean)
-/
@[path]
private lemma bc4c_punctured_cluster_subset_neighbour_cutClusters_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (h0mem : (0 : Site d) ∈ cluster d ω x) :
-- imply
  (cluster d ω x \ {(0 : Site d)}) ⊆ ⋃ n ∈ {n | (openSubgraph d ω).Adj 0 n}, cluster d (removeSite 0 ω) n := by
-- proof
  apply StatMech.Walls.bc4c_punctured_cluster_subset_neighbour_cutClusters ω h0mem

/--
[bc4c_originCutLeavesInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_core.lean)
-/
@[path]
private lemma bc4c_originCutLeavesInfinite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  bc3_OriginCutLeavesInfinite ω := by
-- proof
  apply StatMech.Walls.bc4c_originCutLeavesInfinite ω

/--
[bc4c_threeArms_cutInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_core.lean)
-/
@[path]
private lemma bc4c_threeArms_cutInfinite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
-- given
  (hi1 : (cluster d ω x₁).Infinite)
  (hi2 : (cluster d ω x₂).Infinite)
  (hi3 : (cluster d ω x₃).Infinite) :
-- imply
  ∃ x₁' x₂' x₃' : Site d, x₁' ∈ cluster d ω x₁ ∧ x₂' ∈ cluster d ω x₂ ∧ x₃' ∈ cluster d ω x₃ ∧ (cluster d (removeSite 0 ω) x₁').Infinite ∧ (cluster d (removeSite 0 ω) x₂').Infinite ∧ (cluster d (removeSite 0 ω) x₃').Infinite := by
-- proof
  apply StatMech.Walls.bc4c_threeArms_cutInfinite ω hi1 hi2 hi3

/--
[bc4c_distinctWitnessClusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_core.lean)
-/
@[path]
private lemma bc4c_distinctWitnessClusters_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  bc3_DistinctWitnessClusters d n := by
-- proof
  apply StatMech.Walls.bc4c_distinctWitnessClusters n

/--
[bc4c_arm_cutInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_core.lean)
-/
@[path]
private lemma bc4c_arm_cutInfinite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hinf : (cluster d ω x).Infinite) :
-- imply
  ∃ x', x' ∈ cluster d ω x ∧ (cluster d (removeSite 0 ω) x').Infinite := by
-- proof
  apply StatMech.Walls.bc4c_arm_cutInfinite ω x hinf

/--
[bc4c_closes_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_core.lean)
-/
@[path]
private lemma bc4c_closes_residue_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  bc3_OriginCutLeavesInfinite ω := by
-- proof
  apply StatMech.Walls.bc4c_closes_residue ω


-- created on 2026-10-23
