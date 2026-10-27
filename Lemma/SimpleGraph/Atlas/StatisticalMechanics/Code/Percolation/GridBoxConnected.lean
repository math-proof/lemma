import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
open Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[mk_mem_boxEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/GridBoxConnected.lean)
-/
@[path]
private lemma mk_mem_boxEdges_eq
  {d : ℕ}
  {n : ℕ}
  {x y : Site d}
-- given
  (hx : x ∈ box d n)
  (hy : y ∈ box d n)
  (hadj : (hypercubicLattice d).Adj x y) :
-- imply
  s(x, y) ∈ boxEdges d n := by
-- proof
  apply StatMech.Percolation.mk_mem_boxEdges hx hy hadj

/--
[mem_boxEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/GridBoxConnected.lean)
-/
@[path]
private lemma mem_boxEdges_iff_eq
  {d : ℕ}
  {n : ℕ}
  {x y : Site d} :
-- imply
  s(x, y) ∈ boxEdges d n ↔ x ∈ box d n ∧ y ∈ box d n ∧ (hypercubicLattice d).Adj x y := by
-- proof
  apply StatMech.Percolation.mem_boxEdges_iff

/--
[adj_forceOpen_boxEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/GridBoxConnected.lean)
-/
@[path]
private lemma adj_forceOpen_boxEdges_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hx : x ∈ box d n)
  (hy : y ∈ box d n)
  (hadj : (hypercubicLattice d).Adj x y) :
-- imply
  (openSubgraph d (forceOpenFinset (boxEdges d n) ω)).Adj x y := by
-- proof
  apply StatMech.Percolation.adj_forceOpen_boxEdges ω hx hy hadj

/--
[update_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/GridBoxConnected.lean)
-/
@[path]
private lemma update_mem_box_eq
  {d : ℕ}
  {n : ℕ}
  {x : Site d}
  {j : Fin d}
  {a : ℤ}
-- given
  (hx : x ∈ box d n)
  (ha : a.natAbs ≤ n) :
-- imply
  Function.update x j a ∈ box d n := by
-- proof
  apply StatMech.Percolation.update_mem_box hx j ha

/--
[connected_update_ascend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/GridBoxConnected.lean)
-/
@[path]
private lemma connected_update_ascend_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
-- given
  (hx : x ∈ box d n) :
-- imply
  ∀ (k : ℕ) (a : ℤ), a.natAbs ≤ n → (a + (k : ℤ)).natAbs ≤ n → Connected d (forceOpenFinset (boxEdges d n) ω) (Function.update x j a) (Function.update x j (a + (k : ℤ))) := by
-- proof
  apply StatMech.Percolation.connected_update_ascend ω hx j

/--
[connected_update](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/GridBoxConnected.lean)
-/
@[path]
private lemma connected_update_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
  {a : ℤ}
-- given
  (hx : x ∈ box d n)
  (ha : a.natAbs ≤ n) :
-- imply
  Connected d (forceOpenFinset (boxEdges d n) ω) x (Function.update x j a) := by
-- proof
  apply StatMech.Percolation.connected_update ω hx j ha

/--
[mixSite_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/GridBoxConnected.lean)
-/
@[path]
private lemma mixSite_zero_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  mixSite x y 0 = x := by
-- proof
  apply StatMech.Percolation.mixSite_zero x y

/--
[mixSite_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/GridBoxConnected.lean)
-/
@[path]
private lemma mixSite_full_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  mixSite x y d = y := by
-- proof
  apply StatMech.Percolation.mixSite_full x y

/--
[mixSite_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/GridBoxConnected.lean)
-/
@[path]
private lemma mixSite_mem_box_eq
  {d : ℕ}
  {n : ℕ}
  {x y : Site d}
  {k : ℕ}
-- given
  (hx : x ∈ box d n)
  (hy : y ∈ box d n) :
-- imply
  mixSite x y k ∈ box d n := by
-- proof
  apply StatMech.Percolation.mixSite_mem_box hx hy k

/--
[mixSite_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/GridBoxConnected.lean)
-/
@[path]
private lemma mixSite_succ_eq
  {d : ℕ}
  {x y : Site d}
  {k : ℕ}
-- given
  (hk : k < d) :
-- imply
  mixSite x y (k + 1) = Function.update (mixSite x y k) ⟨k, hk⟩ (y ⟨k, hk⟩) := by
-- proof
  apply StatMech.Percolation.mixSite_succ hk

/--
[connected_mixSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/GridBoxConnected.lean)
-/
@[path]
private lemma connected_mixSite_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hx : x ∈ box d n)
  (hy : y ∈ box d n) :
-- imply
  ∀ k ≤ d, Connected d (forceOpenFinset (boxEdges d n) ω) x (mixSite x y k) := by
-- proof
  apply StatMech.Percolation.connected_mixSite ω hx hy

/--
[box_allOpen_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/GridBoxConnected.lean)
-/
@[path]
private lemma box_allOpen_connected_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hx : x ∈ box d n)
  (hy : y ∈ box d n) :
-- imply
  Connected d (forceOpenFinset (boxEdges d n) ω) x y := by
-- proof
  apply StatMech.Percolation.box_allOpen_connected ω hx hy

/--
[box_allOpen_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/GridBoxConnected.lean)
-/
@[path]
private lemma box_allOpen_reachable_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hx : x ∈ box d n)
  (hy : y ∈ box d n) :
-- imply
  (openSubgraph d (forceOpenFinset (boxEdges d n) ω)).Reachable x y := by
-- proof
  apply StatMech.Percolation.box_allOpen_reachable ω hx hy

/--
[box_allOpen_oneCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/GridBoxConnected.lean)
-/
@[path]
private lemma box_allOpen_oneCluster_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hx : x ∈ box d n) :
-- imply
  box d n ⊆ cluster d (forceOpenFinset (boxEdges d n) ω) x := by
-- proof
  apply StatMech.Percolation.box_allOpen_oneCluster ω hx

/--
[box_allOpen_cluster_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/GridBoxConnected.lean)
-/
@[path]
private lemma box_allOpen_cluster_eq_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hx : x ∈ box d n)
  (hy : y ∈ box d n) :
-- imply
  cluster d (forceOpenFinset (boxEdges d n) ω) x = cluster d (forceOpenFinset (boxEdges d n) ω) y := by
-- proof
  apply StatMech.Percolation.box_allOpen_cluster_eq ω hx hy


-- created on 2026-10-23
