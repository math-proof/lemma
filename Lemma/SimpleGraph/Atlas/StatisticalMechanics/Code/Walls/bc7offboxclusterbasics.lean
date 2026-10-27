import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc7offboxclusterbasics.Part2
open Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Percolation.DisjointPaths StatMech StatMech.Walls


/--
[bc7_farEnd_mem_offBoxCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7offboxclusterbasics.lean)
-/
@[path]
private lemma bc7_farEnd_mem_offBoxCluster_eq
  {d : ℕ}
  {N : ℕ}
  {a : Fin d}
  {R : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hNR : N < R) :
-- imply
  (hrHD_rayPt a (R : ℤ)) ∈ bc6_offBoxCluster N a R ω := by
-- proof
  apply StatMech.Walls.bc7_farEnd_mem_offBoxCluster hNR ω

/--
[bc7_offBoxCluster_subset_offBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7offboxclusterbasics.lean)
-/
@[path]
private lemma bc7_offBoxCluster_subset_offBox_eq
  {d : ℕ}
  {N : ℕ}
  {a : Fin d}
  {R : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  bc6_offBoxCluster N a R ω ⊆ (box d N)ᶜ := by
-- proof
  apply StatMech.Walls.bc7_offBoxCluster_subset_offBox

/--
[bc7_mem_offBoxCluster_offBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7offboxclusterbasics.lean)
-/
@[path]
private lemma bc7_mem_offBoxCluster_offBox_eq
  {d : ℕ}
  {N : ℕ}
  {a : Fin d}
  {R : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hx : x ∈ bc6_offBoxCluster N a R ω) :
-- imply
  x ∉ box d N := by
-- proof
  apply StatMech.Walls.bc7_mem_offBoxCluster_offBox hx

/--
[bc7_offBoxCluster_disjoint_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7offboxclusterbasics.lean)
-/
@[path]
private lemma bc7_offBoxCluster_disjoint_box_eq
  {d : ℕ}
  {N : ℕ}
  {a : Fin d}
  {R : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  Disjoint (bc6_offBoxCluster N a R ω) (box d N) := by
-- proof
  apply StatMech.Walls.bc7_offBoxCluster_disjoint_box

/--
[bc7_offBoxClusterBasics_holds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7offboxclusterbasics.lean)
-/
@[path]
private lemma bc7_offBoxClusterBasics_holds_eq
  {d : ℕ}
  {N : ℕ}
  {a : Fin d}
  {R : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hNR : N < R) :
-- imply
  bc7_offBoxClusterBasics N a R ω := by
-- proof
  apply StatMech.Walls.bc7_offBoxClusterBasics_holds hNR ω

/--
[bc7_offBoxClusterBasics_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7offboxclusterbasics.lean)
-/
@[path]
private lemma bc7_offBoxClusterBasics_iff_eq
  {d : ℕ}
  {N : ℕ}
  {a : Fin d}
  {R : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  bc7_offBoxClusterBasics N a R ω ↔ (hrHD_rayPt a (R : ℤ)) ∈ bc6_offBoxCluster N a R ω ∧ ∀ x ∈ bc6_offBoxCluster N a R ω, x ∉ box d N := by
-- proof
  apply StatMech.Walls.bc7_offBoxClusterBasics_iff


-- created on 2026-10-23
