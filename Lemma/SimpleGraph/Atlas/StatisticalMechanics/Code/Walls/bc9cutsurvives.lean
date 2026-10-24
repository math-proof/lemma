import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc9cutsurvives
open Set SimpleGraph StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech StatMech.Walls


/--
[bc9_removeSite_le_forceOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9cutsurvives.lean)
-/
@[path]
private lemma bc9_removeSite_le_forceOpen_eq
  {d : ℕ}
  {W : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  removeSite (0 : Site d) ω ≤ removeSite (0 : Site d) (forceOpenFinset W ω) := by
-- proof
  apply StatMech.Walls.bc9_removeSite_le_forceOpen W ω

/--
[bc9_cutCluster_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9cutsurvives.lean)
-/
@[path]
private lemma bc9_cutCluster_subset_eq
  {d : ℕ}
  {W : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  cluster d (removeSite (0 : Site d) ω) x ⊆ cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) x := by
-- proof
  apply StatMech.Walls.bc9_cutCluster_subset W ω x

/--
[bc9_connected_of_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9cutsurvives.lean)
-/
@[path]
private lemma bc9_connected_of_base_eq
  {d : ℕ}
  {W : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (h : Connected d (removeSite (0 : Site d) ω) x y) :
-- imply
  Connected d (removeSite (0 : Site d) (forceOpenFinset W ω)) x y := by
-- proof
  apply StatMech.Walls.bc9_connected_of_base W ω h

/--
[bc9_cutCluster_survives_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9cutsurvives.lean)
-/
@[path]
private lemma bc9_cutCluster_survives_infinite_eq
  {d : ℕ}
  {W : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hinf : (cluster d (removeSite (0 : Site d) ω) x).Infinite) :
-- imply
  (cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) x).Infinite := by
-- proof
  apply StatMech.Walls.bc9_cutCluster_survives_infinite W ω hinf

/--
[bc9_reaches_shares_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9cutsurvives.lean)
-/
@[path]
private lemma bc9_reaches_shares_cluster_eq
  {d : ℕ}
  {W : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (h : Connected d (removeSite (0 : Site d) (forceOpenFinset W ω)) x y) :
-- imply
  cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) x = cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) y := by
-- proof
  apply StatMech.Walls.bc9_reaches_shares_cluster W ω h

/--
[bc9_reaches_shares_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9cutsurvives.lean)
-/
@[path]
private lemma bc9_reaches_shares_infinite_eq
  {d : ℕ}
  {W : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hinf : (cluster d (removeSite (0 : Site d) ω) x).Infinite)
  (h : Connected d (removeSite (0 : Site d) (forceOpenFinset W ω)) x y) :
-- imply
  cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) y = cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) x ∧ (cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) y).Infinite := by
-- proof
  apply StatMech.Walls.bc9_reaches_shares_infinite W ω hinf h

/--
[bc9_cut_survives](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9cutsurvives.lean)
-/
@[path]
private lemma bc9_cut_survives_eq
  {d : ℕ}
  {W : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (_hW : ∀ e ∈ W, (0 : Site d) ∉ e)
  (hinf : (cluster d (removeSite (0 : Site d) ω) x).Infinite) :
-- imply
  (cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) x).Infinite ∧ ∀ y, Connected d (removeSite (0 : Site d) (forceOpenFinset W ω)) x y → cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) y = cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) x ∧ (cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) y).Infinite := by
-- proof
  apply StatMech.Walls.bc9_cut_survives W ω _hW hinf

/--
[bc9_origin_isolated_of_avoiding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9cutsurvives.lean)
-/
@[path]
private lemma bc9_origin_isolated_of_avoiding_eq
  {d : ℕ}
  {W : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {v : Site d}
-- given
  (_hW : ∀ e ∈ W, (0 : Site d) ∉ e) :
-- imply
  ¬ (openSubgraph d (removeSite (0 : Site d) (forceOpenFinset W ω))).Adj 0 v := by
-- proof
  apply StatMech.Walls.bc9_origin_isolated_of_avoiding W ω _hW v

/--
[bc9_cut_survives_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9cutsurvives.lean)
-/
@[path]
private lemma bc9_cut_survives_self_eq
  {d : ℕ}
  {W : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hW : ∀ e ∈ W, (0 : Site d) ∉ e)
  (hinf : (cluster d (removeSite (0 : Site d) ω) 0).Infinite) :
-- imply
  (cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) 0).Infinite ∧ ∀ y, Connected d (removeSite (0 : Site d) (forceOpenFinset W ω)) 0 y → cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) y = cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) 0 ∧ (cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) y).Infinite := by
-- proof
  apply StatMech.Walls.bc9_cut_survives_self W ω hW hinf

/--
[bc9_cutCluster_eq_of_originIncident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9cutsurvives.lean)
-/
@[path]
private lemma bc9_cutCluster_eq_of_originIncident_eq
  {d : ℕ}
  {F : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a : Site d}
-- given
  (hF : ∀ e ∈ F, (0 : Site d) ∈ e) :
-- imply
  cluster d (removeSite (0 : Site d) (forceOpenFinset F ω)) a = cluster d (removeSite (0 : Site d) ω) a := by
-- proof
  apply StatMech.Walls.bc9_cutCluster_eq_of_originIncident F ω hF a


-- created on 2026-10-23
