import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc5_barrierblocks.Part2
open Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Percolation.DisjointPaths StatMech StatMech.Walls


/--
[bc5_cluster_subset_of_adjClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_barrierblocks.lean)
-/
@[path]
private lemma bc5_cluster_subset_of_adjClosed_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))}
  {R : Set (Site d)}
  {a : Site d}
-- given
  (ha : a ∈ R)
  (hcl : bc5_AdjClosed ϱ R) :
-- imply
  cluster d ϱ a ⊆ R := by
-- proof
  apply StatMech.Walls.bc5_cluster_subset_of_adjClosed ϱ R a ha hcl

/--
[bc5_mem_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_barrierblocks.lean)
-/
@[path]
private lemma bc5_mem_of_connected_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))}
  {R : Set (Site d)}
  {p q : Site d}
-- given
  (hcl : bc5_AdjClosed ϱ R)
  (hp : p ∈ R)
  (hconn : Connected d ϱ p q) :
-- imply
  q ∈ R := by
-- proof
  apply StatMech.Walls.bc5_mem_of_connected ϱ R p q hcl hp hconn

/--
[bc5_barrier_blocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_barrierblocks.lean)
-/
@[path]
private lemma bc5_barrier_blocks_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))}
  {R : Set (Site d)}
  {p q : Site d}
-- given
  (hcl : bc5_AdjClosed ϱ R)
  (hp : p ∈ R)
  (hq : q ∉ R) :
-- imply
  ¬ Connected d ϱ p q := by
-- proof
  apply StatMech.Walls.bc5_barrier_blocks ϱ R p q hcl hp hq

/--
[bc5_barrier_blocks_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_barrierblocks.lean)
-/
@[path]
private lemma bc5_barrier_blocks_symm_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))}
  {R : Set (Site d)}
  {p q : Site d}
-- given
  (hcl : bc5_AdjClosed ϱ R)
  (hp : p ∈ R)
  (hq : q ∉ R) :
-- imply
  ¬ Connected d ϱ q p := by
-- proof
  apply StatMech.Walls.bc5_barrier_blocks_symm ϱ R p q hcl hp hq

/--
[bc5_disconnected_of_barrier_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_barrierblocks.lean)
-/
@[path]
private lemma bc5_disconnected_of_barrier_split_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))}
  {R : Set (Site d)}
  {p q : Site d}
-- given
  (hcl : bc5_AdjClosed ϱ R)
  (hp : p ∈ R)
  (hq : q ∉ R) :
-- imply
  ¬ Connected d ϱ p q ∧ ¬ Connected d ϱ q p := by
-- proof
  apply StatMech.Walls.bc5_disconnected_of_barrier_split ϱ R p q hcl hp hq

/--
[bc5_cluster_adjClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_barrierblocks.lean)
-/
@[path]
private lemma bc5_cluster_adjClosed_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))}
  {w : Site d} :
-- imply
  bc5_AdjClosed ϱ (cluster d ϱ w) := by
-- proof
  apply StatMech.Walls.bc5_cluster_adjClosed ϱ w

/--
[bc5_compl_cluster_adjClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_barrierblocks.lean)
-/
@[path]
private lemma bc5_compl_cluster_adjClosed_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))}
  {w : Site d} :
-- imply
  bc5_AdjClosed ϱ (cluster d ϱ w)ᶜ := by
-- proof
  apply StatMech.Walls.bc5_compl_cluster_adjClosed ϱ w

/--
[bc5_barrier_blocks_iff_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_barrierblocks.lean)
-/
@[path]
private lemma bc5_barrier_blocks_iff_cluster_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))}
  {p q : Site d} :
-- imply
  (¬ Connected d ϱ p q) ↔ ∃ R : Set (Site d), bc5_AdjClosed ϱ R ∧ p ∈ R ∧ q ∉ R := by
-- proof
  apply StatMech.Walls.bc5_barrier_blocks_iff_cluster ϱ p q

/--
[bc5_pairwiseSeparated_of_barriers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_barrierblocks.lean)
-/
@[path]
private lemma bc5_pairwiseSeparated_of_barriers_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j₁ j₂ j₃ : Fin d}
  {L₁ L₂ L₃ : ℕ}
  {R₁₂ R₁₃ R₂₃ : Set (Site d)}
-- given
  (hcl12 : bc5_AdjClosed (bc5_corridorCut ω j₁ j₂ j₃ L₁ L₂ L₃) R₁₂)
  (h12p : hrHD_rayPt j₁ 1 ∈ R₁₂)
  (h12q : hrHD_rayPt j₂ 1 ∉ R₁₂)
  (hcl13 : bc5_AdjClosed (bc5_corridorCut ω j₁ j₂ j₃ L₁ L₂ L₃) R₁₃)
  (h13p : hrHD_rayPt j₁ 1 ∈ R₁₃)
  (h13q : hrHD_rayPt j₃ 1 ∉ R₁₃)
  (hcl23 : bc5_AdjClosed (bc5_corridorCut ω j₁ j₂ j₃ L₁ L₂ L₃) R₂₃)
  (h23p : hrHD_rayPt j₂ 1 ∈ R₂₃)
  (h23q : hrHD_rayPt j₃ 1 ∉ R₂₃) :
-- imply
  bc2_PairwiseSeparated ω j₁ j₂ j₃ L₁ L₂ L₃ := by
-- proof
  apply StatMech.Walls.bc5_pairwiseSeparated_of_barriers ω j₁ j₂ j₃ L₁ L₂ L₃ R₁₂ R₁₃ R₂₃ hcl12 h12p h12q hcl13 h13p h13q hcl23 h23p h23q

/--
[bc5_pairwiseSeparated_of_clusterBarriers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_barrierblocks.lean)
-/
@[path]
private lemma bc5_pairwiseSeparated_of_clusterBarriers_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j₁ j₂ j₃ : Fin d}
  {L₁ L₂ L₃ : ℕ}
-- given
  (h12 : ¬ Connected d (bc5_corridorCut ω j₁ j₂ j₃ L₁ L₂ L₃) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1))
  (h13 : ¬ Connected d (bc5_corridorCut ω j₁ j₂ j₃ L₁ L₂ L₃) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₃ 1))
  (h23 : ¬ Connected d (bc5_corridorCut ω j₁ j₂ j₃ L₁ L₂ L₃) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)) :
-- imply
  bc2_PairwiseSeparated ω j₁ j₂ j₃ L₁ L₂ L₃ := by
-- proof
  apply StatMech.Walls.bc5_pairwiseSeparated_of_clusterBarriers ω j₁ j₂ j₃ L₁ L₂ L₃ h12 h13 h23

/--
[bc5_pairwiseSeparated_iff_cutDisconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_barrierblocks.lean)
-/
@[path]
private lemma bc5_pairwiseSeparated_iff_cutDisconnected_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j₁ j₂ j₃ : Fin d}
  {L₁ L₂ L₃ : ℕ} :
-- imply
  bc2_PairwiseSeparated ω j₁ j₂ j₃ L₁ L₂ L₃ ↔ (¬ Connected d (bc5_corridorCut ω j₁ j₂ j₃ L₁ L₂ L₃) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) ∧ ¬ Connected d (bc5_corridorCut ω j₁ j₂ j₃ L₁ L₂ L₃) (hrHD_rayPt j₁ 1) (hrHD_rayPt j₃ 1) ∧ ¬ Connected d (bc5_corridorCut ω j₁ j₂ j₃ L₁ L₂ L₃) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)) := by
-- proof
  apply StatMech.Walls.bc5_pairwiseSeparated_iff_cutDisconnected ω j₁ j₂ j₃ L₁ L₂ L₃

/--
[bc5_barrierblocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_barrierblocks.lean)
-/
@[path]
private lemma bc5_barrierblocks_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))} :
-- imply
  (∀ (R : Set (Site d)) (p q : Site d), bc5_AdjClosed ϱ R → p ∈ R → q ∉ R → ¬ Connected d ϱ p q ∧ ¬ Connected d ϱ q p) ∧ (∀ p q : Site d, (¬ Connected d ϱ p q) ↔ ∃ R : Set (Site d), bc5_AdjClosed ϱ R ∧ p ∈ R ∧ q ∉ R) := by
-- proof
  apply StatMech.Walls.bc5_barrierblocks ϱ


-- created on 2026-10-23
