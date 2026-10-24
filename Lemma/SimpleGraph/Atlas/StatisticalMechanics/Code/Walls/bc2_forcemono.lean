import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc2_forcemono
open Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bc2_force_mono_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcemono.lean)
-/
@[path]
private lemma bc2_force_mono_base_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))} :
-- imply
  ω ≤ forceOpenFinset W ω := by
-- proof
  apply StatMech.Walls.bc2_force_mono_base ω W

/--
[bc2_force_mono_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcemono.lean)
-/
@[path]
private lemma bc2_force_mono_cut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
  {x : Site d} :
-- imply
  removeSite x ω ≤ removeSite x (forceOpenFinset W ω) := by
-- proof
  apply StatMech.Walls.bc2_force_mono_cut ω W x

/--
[bc2_force_mono_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcemono.lean)
-/
@[path]
private lemma bc2_force_mono_origin_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))} :
-- imply
  removeSite (0 : Site d) ω ≤ removeSite (0 : Site d) (forceOpenFinset W ω) := by
-- proof
  apply StatMech.Walls.bc2_force_mono_origin ω W

/--
[bc2_connected_force_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcemono.lean)
-/
@[path]
private lemma bc2_connected_force_mono_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
  {a b : Site d}
-- given
  (h : Connected d ω a b) :
-- imply
  Connected d (forceOpenFinset W ω) a b := by
-- proof
  apply StatMech.Walls.bc2_connected_force_mono ω W h

/--
[bc2_connected_force_mono_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcemono.lean)
-/
@[path]
private lemma bc2_connected_force_mono_cut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
  {x : Site d}
  {a b : Site d}
-- given
  (h : Connected d (removeSite x ω) a b) :
-- imply
  Connected d (removeSite x (forceOpenFinset W ω)) a b := by
-- proof
  apply StatMech.Walls.bc2_connected_force_mono_cut ω W x h

/--
[bc2_cluster_force_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcemono.lean)
-/
@[path]
private lemma bc2_cluster_force_mono_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
  {y : Site d} :
-- imply
  cluster d ω y ⊆ cluster d (forceOpenFinset W ω) y := by
-- proof
  apply StatMech.Walls.bc2_cluster_force_mono ω W y

/--
[bc2_cluster_force_mono_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcemono.lean)
-/
@[path]
private lemma bc2_cluster_force_mono_cut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
  {x : Site d}
  {y : Site d} :
-- imply
  cluster d (removeSite x ω) y ⊆ cluster d (removeSite x (forceOpenFinset W ω)) y := by
-- proof
  apply StatMech.Walls.bc2_cluster_force_mono_cut ω W x y

/--
[bc2_clusterInfinite_force_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcemono.lean)
-/
@[path]
private lemma bc2_clusterInfinite_force_mono_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
  {y : Site d}
-- given
  (h : (cluster d ω y).Infinite) :
-- imply
  (cluster d (forceOpenFinset W ω) y).Infinite := by
-- proof
  apply StatMech.Walls.bc2_clusterInfinite_force_mono ω W h

/--
[bc2_clusterInfinite_force_mono_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcemono.lean)
-/
@[path]
private lemma bc2_clusterInfinite_force_mono_cut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
  {x : Site d}
  {y : Site d}
-- given
  (h : (cluster d (removeSite x ω) y).Infinite) :
-- imply
  (cluster d (removeSite x (forceOpenFinset W ω)) y).Infinite := by
-- proof
  apply StatMech.Walls.bc2_clusterInfinite_force_mono_cut ω W x h

/--
[bc2_connected_force_mono_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcemono.lean)
-/
@[path]
private lemma bc2_connected_force_mono_origin_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {a b : Site d}
-- given
  (h : Connected d (removeSite (0 : Site d) ω) a b) :
-- imply
  Connected d (removeSite (0 : Site d) (forceOpenFinset G ω)) a b := by
-- proof
  apply StatMech.Walls.bc2_connected_force_mono_origin ω G h

/--
[bc2_clusterInfinite_force_mono_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcemono.lean)
-/
@[path]
private lemma bc2_clusterInfinite_force_mono_origin_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {y : Site d}
-- given
  (h : (cluster d (removeSite (0 : Site d) ω) y).Infinite) :
-- imply
  (cluster d (removeSite (0 : Site d) (forceOpenFinset G ω)) y).Infinite := by
-- proof
  apply StatMech.Walls.bc2_clusterInfinite_force_mono_origin ω G h


-- created on 2026-10-23
