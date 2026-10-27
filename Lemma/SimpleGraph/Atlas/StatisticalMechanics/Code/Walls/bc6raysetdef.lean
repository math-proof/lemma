import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc6raysetdef.Part3
open Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Percolation.DisjointPaths StatMech StatMech.Walls


/--
[bc6_mem_rayInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6raysetdef.lean)
-/
@[path]
private lemma bc6_mem_rayInterior_eq
  {d : ℕ}
  {a : Fin d}
  {R : ℕ}
  {x : Site d} :
-- imply
  x ∈ bc6_rayInterior a R ↔ ∃ p : ℕ, (1 ≤ p ∧ p ≤ R) ∧ x = hrHD_rayPt a (p : ℤ) := by
-- proof
  apply StatMech.Walls.bc6_mem_rayInterior

/--
[bc6_rayPt_mem_rayInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6raysetdef.lean)
-/
@[path]
private lemma bc6_rayPt_mem_rayInterior_eq
  {d : ℕ}
  {a : Fin d}
  {R p : ℕ}
-- given
  (h0 : 1 ≤ p)
  (h1 : p ≤ R) :
-- imply
  hrHD_rayPt a (p : ℤ) ∈ bc6_rayInterior a R := by
-- proof
  apply StatMech.Walls.bc6_rayPt_mem_rayInterior h0 h1

/--
[bc6_mouth_mem_rayInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6raysetdef.lean)
-/
@[path]
private lemma bc6_mouth_mem_rayInterior_eq
  {d : ℕ}
  {a : Fin d}
  {R : ℕ}
-- given
  (hR : 1 ≤ R) :
-- imply
  (hrHD_rayPt a 1 : Site d) ∈ bc6_rayInterior a R := by
-- proof
  apply StatMech.Walls.bc6_mouth_mem_rayInterior hR

/--
[bc6_origin_notMem_rayInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6raysetdef.lean)
-/
@[path]
private lemma bc6_origin_notMem_rayInterior_eq
  {d : ℕ}
  {a : Fin d}
  {R : ℕ} :
-- imply
  (0 : Site d) ∉ bc6_rayInterior a R := by
-- proof
  apply StatMech.Walls.bc6_origin_notMem_rayInterior

/--
[bc6_offBoxCluster_subset_offBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6raysetdef.lean)
-/
@[path]
private lemma bc6_offBoxCluster_subset_offBox_eq
  {d : ℕ}
  {N : ℕ}
  {a : Fin d}
  {R : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  bc6_offBoxCluster N a R ω ⊆ (box d N)ᶜ := by
-- proof
  apply StatMech.Walls.bc6_offBoxCluster_subset_offBox

/--
[bc6_mem_offBoxCluster_offBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6raysetdef.lean)
-/
@[path]
private lemma bc6_mem_offBoxCluster_offBox_eq
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
  apply StatMech.Walls.bc6_mem_offBoxCluster_offBox hx

/--
[bc6_farEnd_notMem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6raysetdef.lean)
-/
@[path]
private lemma bc6_farEnd_notMem_box_eq
  {d : ℕ}
  {N : ℕ}
  {a : Fin d}
  {R : ℕ}
-- given
  (hNR : N < R) :
-- imply
  (hrHD_rayPt a (R : ℤ)) ∉ box d N := by
-- proof
  apply StatMech.Walls.bc6_farEnd_notMem_box hNR

/--
[bc6_farEnd_mem_offBoxCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6raysetdef.lean)
-/
@[path]
private lemma bc6_farEnd_mem_offBoxCluster_eq
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
  apply StatMech.Walls.bc6_farEnd_mem_offBoxCluster hNR ω

/--
[bc6_mem_armRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6raysetdef.lean)
-/
@[path]
private lemma bc6_mem_armRegion_eq
  {d : ℕ}
  {N : ℕ}
  {a : Fin d}
  {R : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  x ∈ bc6_armRegion N a R ω ↔ x ∈ bc6_rayInterior a R ∨ x ∈ bc6_offBoxCluster N a R ω := by
-- proof
  apply StatMech.Walls.bc6_mem_armRegion

/--
[bc6_rayInterior_subset_armRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6raysetdef.lean)
-/
@[path]
private lemma bc6_rayInterior_subset_armRegion_eq
  {d : ℕ}
  {N : ℕ}
  {a : Fin d}
  {R : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  bc6_rayInterior a R ⊆ bc6_armRegion N a R ω := by
-- proof
  apply StatMech.Walls.bc6_rayInterior_subset_armRegion

/--
[bc6_offBoxCluster_subset_armRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6raysetdef.lean)
-/
@[path]
private lemma bc6_offBoxCluster_subset_armRegion_eq
  {d : ℕ}
  {N : ℕ}
  {a : Fin d}
  {R : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  bc6_offBoxCluster N a R ω ⊆ bc6_armRegion N a R ω := by
-- proof
  apply StatMech.Walls.bc6_offBoxCluster_subset_armRegion

/--
[bc6_rayPt_mem_armRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6raysetdef.lean)
-/
@[path]
private lemma bc6_rayPt_mem_armRegion_eq
  {d : ℕ}
  {N : ℕ}
  {a : Fin d}
  {R p : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h0 : 1 ≤ p)
  (h1 : p ≤ R) :
-- imply
  hrHD_rayPt a (p : ℤ) ∈ bc6_armRegion N a R ω := by
-- proof
  apply StatMech.Walls.bc6_rayPt_mem_armRegion h0 h1

/--
[bc6_mouth_mem_armRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6raysetdef.lean)
-/
@[path]
private lemma bc6_mouth_mem_armRegion_eq
  {d : ℕ}
  {N : ℕ}
  {a : Fin d}
  {R : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hR : 1 ≤ R) :
-- imply
  (hrHD_rayPt a 1 : Site d) ∈ bc6_armRegion N a R ω := by
-- proof
  apply StatMech.Walls.bc6_mouth_mem_armRegion hR

/--
[bc6_farEnd_mem_armRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6raysetdef.lean)
-/
@[path]
private lemma bc6_farEnd_mem_armRegion_eq
  {d : ℕ}
  {N : ℕ}
  {a : Fin d}
  {R : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hNR : N < R) :
-- imply
  (hrHD_rayPt a (R : ℤ)) ∈ bc6_armRegion N a R ω := by
-- proof
  apply StatMech.Walls.bc6_farEnd_mem_armRegion hNR ω


-- created on 2026-10-23
