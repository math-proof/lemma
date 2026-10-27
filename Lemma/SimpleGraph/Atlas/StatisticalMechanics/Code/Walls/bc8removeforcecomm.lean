import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc8removeforcecomm
open Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech StatMech.Walls


/--
[bc8_removeSite_forceOpen_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8removeforcecomm.lean)
-/
@[path]
private lemma bc8_removeSite_forceOpen_comm_eq
  {d : ℕ}
  {F : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hF : ∀ e ∈ F, (0 : Site d) ∈ e) :
-- imply
  removeSite (0 : Site d) (forceOpenFinset F ω) = removeSite (0 : Site d) ω := by
-- proof
  apply StatMech.Walls.bc8_removeSite_forceOpen_comm F ω hF

/--
[bc8_removeSite_forceOpen_comm_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8removeforcecomm.lean)
-/
@[path]
private lemma bc8_removeSite_forceOpen_comm_general_eq
  {d : ℕ}
  {x : Site d}
  {F : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hF : ∀ e ∈ F, x ∈ e) :
-- imply
  removeSite x (forceOpenFinset F ω) = removeSite x ω := by
-- proof
  apply StatMech.Walls.bc8_removeSite_forceOpen_comm_general x F ω hF

/--
[bc8_openSubgraph_forceOpen_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8removeforcecomm.lean)
-/
@[path]
private lemma bc8_openSubgraph_forceOpen_eq_eq
  {d : ℕ}
  {F : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hF : ∀ e ∈ F, (0 : Site d) ∈ e) :
-- imply
  openSubgraph d (removeSite (0 : Site d) (forceOpenFinset F ω)) = openSubgraph d (removeSite (0 : Site d) ω) := by
-- proof
  apply StatMech.Walls.bc8_openSubgraph_forceOpen_eq F ω hF

/--
[bc8_connected_forceOpen_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8removeforcecomm.lean)
-/
@[path]
private lemma bc8_connected_forceOpen_iff_eq
  {d : ℕ}
  {F : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u v : Site d}
-- given
  (hF : ∀ e ∈ F, (0 : Site d) ∈ e) :
-- imply
  Connected d (removeSite (0 : Site d) (forceOpenFinset F ω)) u v ↔ Connected d (removeSite (0 : Site d) ω) u v := by
-- proof
  apply StatMech.Walls.bc8_connected_forceOpen_iff F ω hF u v

/--
[bc8_cluster_forceOpen_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8removeforcecomm.lean)
-/
@[path]
private lemma bc8_cluster_forceOpen_eq_eq
  {d : ℕ}
  {F : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a : Site d}
-- given
  (hF : ∀ e ∈ F, (0 : Site d) ∈ e) :
-- imply
  cluster d (removeSite (0 : Site d) (forceOpenFinset F ω)) a = cluster d (removeSite (0 : Site d) ω) a := by
-- proof
  apply StatMech.Walls.bc8_cluster_forceOpen_eq F ω hF a


-- created on 2026-10-23
