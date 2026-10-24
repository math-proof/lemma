import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc3_barrierblocks
open Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Percolation.DisjointPaths StatMech StatMech.Walls


/--
[bc3_cluster_subset_of_adjClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_barrierblocks.lean)
-/
@[path]
private lemma bc3_cluster_subset_of_adjClosed_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))}
  {R : Set (Site d)}
  {a : Site d}
-- given
  (ha : a ∈ R)
  (hcl : bc3_AdjClosed ϱ R) :
-- imply
  cluster d ϱ a ⊆ R := by
-- proof
  apply StatMech.Walls.bc3_cluster_subset_of_adjClosed ϱ R a ha hcl

/--
[bc3_barrier_blocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_barrierblocks.lean)
-/
@[path]
private lemma bc3_barrier_blocks_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))}
  {R : Set (Site d)}
  {p q : Site d}
-- given
  (hcl : bc3_AdjClosed ϱ R)
  (hp : p ∈ R)
  (hq : q ∉ R) :
-- imply
  ¬ Connected d ϱ p q := by
-- proof
  apply StatMech.Walls.bc3_barrier_blocks ϱ R p q hcl hp hq

/--
[bc3_barrier_blocks_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_barrierblocks.lean)
-/
@[path]
private lemma bc3_barrier_blocks_symm_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))}
  {R : Set (Site d)}
  {p q : Site d}
-- given
  (hcl : bc3_AdjClosed ϱ R)
  (hp : p ∈ R)
  (hq : q ∉ R) :
-- imply
  ¬ Connected d ϱ q p := by
-- proof
  apply StatMech.Walls.bc3_barrier_blocks_symm ϱ R p q hcl hp hq

/--
[bc3_mem_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_barrierblocks.lean)
-/
@[path]
private lemma bc3_mem_of_connected_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))}
  {R : Set (Site d)}
  {p q : Site d}
-- given
  (hcl : bc3_AdjClosed ϱ R)
  (hp : p ∈ R)
  (hconn : Connected d ϱ p q) :
-- imply
  q ∈ R := by
-- proof
  apply StatMech.Walls.bc3_mem_of_connected ϱ R p q hcl hp hconn

/--
[bc3_disconnected_of_barrier_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_barrierblocks.lean)
-/
@[path]
private lemma bc3_disconnected_of_barrier_split_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))}
  {R : Set (Site d)}
  {p q : Site d}
-- given
  (hcl : bc3_AdjClosed ϱ R)
  (hp : p ∈ R)
  (hq : q ∉ R) :
-- imply
  ¬ Connected d ϱ p q ∧ ¬ Connected d ϱ q p := by
-- proof
  apply StatMech.Walls.bc3_disconnected_of_barrier_split ϱ R p q hcl hp hq

/--
[bc3_cluster_adjClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_barrierblocks.lean)
-/
@[path]
private lemma bc3_cluster_adjClosed_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))}
  {w : Site d} :
-- imply
  bc3_AdjClosed ϱ (cluster d ϱ w) := by
-- proof
  apply StatMech.Walls.bc3_cluster_adjClosed ϱ w

/--
[bc3_compl_cluster_adjClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_barrierblocks.lean)
-/
@[path]
private lemma bc3_compl_cluster_adjClosed_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))}
  {w : Site d} :
-- imply
  bc3_AdjClosed ϱ (cluster d ϱ w)ᶜ := by
-- proof
  apply StatMech.Walls.bc3_compl_cluster_adjClosed ϱ w

/--
[bc3_barrier_blocks_iff_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_barrierblocks.lean)
-/
@[path]
private lemma bc3_barrier_blocks_iff_cluster_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))}
  {p q : Site d} :
-- imply
  (¬ Connected d ϱ p q) ↔ ∃ R : Set (Site d), bc3_AdjClosed ϱ R ∧ p ∈ R ∧ q ∉ R := by
-- proof
  apply StatMech.Walls.bc3_barrier_blocks_iff_cluster ϱ p q

/--
[bc3_barrierblocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_barrierblocks.lean)
-/
@[path]
private lemma bc3_barrierblocks_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))} :
-- imply
  (∀ (R : Set (Site d)) (p q : Site d), bc3_AdjClosed ϱ R → p ∈ R → q ∉ R → ¬ Connected d ϱ p q ∧ ¬ Connected d ϱ q p) ∧ (∀ p q : Site d, (¬ Connected d ϱ p q) ↔ ∃ R : Set (Site d), bc3_AdjClosed ϱ R ∧ p ∈ R ∧ q ∉ R) := by
-- proof
  apply StatMech.Walls.bc3_barrierblocks ϱ


-- created on 2026-10-23
