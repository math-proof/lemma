import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc2_forcededgeopen.Part2
open Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech StatMech.Walls


/--
[bc2_forced_edge_open_eq_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcededgeopen.lean)
-/
@[path]
private lemma bc2_forced_edge_open_eq_true_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
  {u v : Site d}
-- given
  (hmem : s(u, v) ∈ W)
  (h0 : (0 : Site d) ∉ s(u, v)) :
-- imply
  removeSite 0 (forceOpenFinset W ω) s(u, v) = true := by
-- proof
  apply StatMech.Walls.bc2_forced_edge_open_eq_true ω W hmem h0

/--
[bc2_forced_edge_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcededgeopen.lean)
-/
@[path]
private lemma bc2_forced_edge_open_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
  {u v : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj u v)
  (hmem : s(u, v) ∈ W)
  (h0 : (0 : Site d) ∉ s(u, v)) :
-- imply
  IsOpenEdge d (removeSite 0 (forceOpenFinset W ω)) u v := by
-- proof
  apply StatMech.Walls.bc2_forced_edge_open ω W hadj hmem h0

/--
[bc2_forced_edge_open_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcededgeopen.lean)
-/
@[path]
private lemma bc2_forced_edge_open_mem_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
  {e : Sym2 (Site d)}
-- given
  (hmem : e ∈ W)
  (h0 : (0 : Site d) ∉ e) :
-- imply
  removeSite 0 (forceOpenFinset W ω) e = true := by
-- proof
  apply StatMech.Walls.bc2_forced_edge_open_mem ω W hmem h0

/--
[bc2_forced_edge_open_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcededgeopen.lean)
-/
@[path]
private lemma bc2_forced_edge_open_all_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
-- given
  (hW : bc2_IsLatticeWiring W) :
-- imply
  ∀ u v : Site d, s(u, v) ∈ W → (0 : Site d) ∉ s(u, v) → IsOpenEdge d (removeSite 0 (forceOpenFinset W ω)) u v := by
-- proof
  apply StatMech.Walls.bc2_forced_edge_open_all ω W hW

/--
[bc2_corridor_isLatticeWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcededgeopen.lean)
-/
@[path]
private lemma bc2_corridor_isLatticeWiring_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ} :
-- imply
  bc2_IsLatticeWiring (hrHD_corridorEdges j L) := by
-- proof
  apply StatMech.Walls.bc2_corridor_isLatticeWiring j L

/--
[bc2_forced_edge_open_corridor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcededgeopen.lean)
-/
@[path]
private lemma bc2_forced_edge_open_corridor_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ} :
-- imply
  ∀ u v : Site d, s(u, v) ∈ hrHD_corridorEdges j L → (0 : Site d) ∉ s(u, v) → IsOpenEdge d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j L) ω)) u v := by
-- proof
  apply StatMech.Walls.bc2_forced_edge_open_corridor ω j L

/--
[bc2_forced_edge_open_interior_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcededgeopen.lean)
-/
@[path]
private lemma bc2_forced_edge_open_interior_step_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L t : ℕ}
-- given
  (ht : t < L) :
-- imply
  IsOpenEdge d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)) (hrHD_rayPt j ((t : ℤ) + 1)) (hrHD_rayPt j ((t : ℤ) + 2)) := by
-- proof
  apply StatMech.Walls.bc2_forced_edge_open_interior_step ω j L t ht


-- created on 2026-10-23
