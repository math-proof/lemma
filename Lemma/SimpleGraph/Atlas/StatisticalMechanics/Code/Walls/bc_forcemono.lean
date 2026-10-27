import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc_forcemono
open Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bc_force_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_forcemono.lean)
-/
@[path]
private lemma bc_force_mono_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))} :
-- imply
  removeSite (0 : Site d) ω ≤ removeSite (0 : Site d) (forceOpenFinset W ω) := by
-- proof
  apply StatMech.Walls.bc_force_mono ω W

/--
[bc_connected_force_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_forcemono.lean)
-/
@[path]
private lemma bc_connected_force_mono_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
  {a b : Site d}
-- given
  (h : Connected d (removeSite (0 : Site d) ω) a b) :
-- imply
  Connected d (removeSite (0 : Site d) (forceOpenFinset W ω)) a b := by
-- proof
  apply StatMech.Walls.bc_connected_force_mono ω W h

/--
[bc_cluster_force_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_forcemono.lean)
-/
@[path]
private lemma bc_cluster_force_mono_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
  {x : Site d} :
-- imply
  cluster d (removeSite (0 : Site d) ω) x ⊆ cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) x := by
-- proof
  apply StatMech.Walls.bc_cluster_force_mono ω W x

/--
[bc_clusterInfinite_force_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_forcemono.lean)
-/
@[path]
private lemma bc_clusterInfinite_force_mono_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
  {x : Site d}
-- given
  (h : (cluster d (removeSite (0 : Site d) ω) x).Infinite) :
-- imply
  (cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) x).Infinite := by
-- proof
  apply StatMech.Walls.bc_clusterInfinite_force_mono ω W h


-- created on 2026-10-23
