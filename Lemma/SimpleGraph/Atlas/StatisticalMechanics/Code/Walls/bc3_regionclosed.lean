import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc3_regionclosed.Part2
open Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech StatMech.Walls


/--
[bc3_rho_edge_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_regionclosed.lean)
-/
@[path]
private lemma bc3_rho_edge_cases_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {e : Sym2 (Site d)}
-- given
  (hopen : removeSite 0 (forceOpenFinset G ω) e = true) :
-- imply
  (0 : Site d) ∉ e ∧ (e ∈ G ∨ ω e = true) := by
-- proof
  apply StatMech.Walls.bc3_rho_edge_cases ω G hopen

/--
[bc3_region_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_regionclosed.lean)
-/
@[path]
private lemma bc3_region_closed_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {R : Set (Site d)}
-- given
  (hω : bc3_ClosedUnderOmega ω R)
  (hG : bc3_ClosedUnderWiring G R) :
-- imply
  bc3_ClosedUnderRho ω G R := by
-- proof
  apply StatMech.Walls.bc3_region_closed ω G R hω hG

/--
[bc3_omega_open_to_rho](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_regionclosed.lean)
-/
@[path]
private lemma bc3_omega_open_to_rho_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {x y : Site d}
-- given
  (h : IsOpenEdge d ω x y)
  (h0 : (0 : Site d) ∉ s(x, y)) :
-- imply
  IsOpenEdge d (removeSite 0 (forceOpenFinset G ω)) x y := by
-- proof
  apply StatMech.Walls.bc3_omega_open_to_rho G h h0

/--
[bc3_closedUnderWiring_of_rho](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_regionclosed.lean)
-/
@[path]
private lemma bc3_closedUnderWiring_of_rho_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {R : Set (Site d)}
-- given
  (hϱ : bc3_ClosedUnderRho ω G R) :
-- imply
  bc3_ClosedUnderWiring G R := by
-- proof
  apply StatMech.Walls.bc3_closedUnderWiring_of_rho ω G R hϱ

/--
[bc3_closedUnderOmega_of_rho](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_regionclosed.lean)
-/
@[path]
private lemma bc3_closedUnderOmega_of_rho_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {R : Set (Site d)}
-- given
  (hϱ : bc3_ClosedUnderRho ω G R) :
-- imply
  ∀ ⦃x y : Site d⦄, x ∈ R → IsOpenEdge d ω x y → (0 : Site d) ∉ s(x, y) → y ∈ R := by
-- proof
  apply StatMech.Walls.bc3_closedUnderOmega_of_rho ω G R hϱ

/--
[bc3_reachable_mem_of_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_regionclosed.lean)
-/
@[path]
private lemma bc3_reachable_mem_of_closed_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {R : Set (Site d)}
  {x y : Site d}
-- given
  (hclosed : bc3_ClosedUnderRho ω G R)
  (hxR : x ∈ R)
  (hconn : Connected d (removeSite 0 (forceOpenFinset G ω)) x y) :
-- imply
  y ∈ R := by
-- proof
  apply StatMech.Walls.bc3_reachable_mem_of_closed ω G R hclosed hxR hconn

/--
[bc3_cluster_subset_of_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_regionclosed.lean)
-/
@[path]
private lemma bc3_cluster_subset_of_closed_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {R : Set (Site d)}
  {x : Site d}
-- given
  (hω : bc3_ClosedUnderOmega ω R)
  (hG : bc3_ClosedUnderWiring G R)
  (hxR : x ∈ R) :
-- imply
  cluster d (removeSite 0 (forceOpenFinset G ω)) x ⊆ R := by
-- proof
  apply StatMech.Walls.bc3_cluster_subset_of_closed ω G R hω hG hxR

/--
[bc3_univ_closedUnderRho](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_regionclosed.lean)
-/
@[path]
private lemma bc3_univ_closedUnderRho_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))} :
-- imply
  bc3_ClosedUnderRho ω G (Set.univ : Set (Site d)) := by
-- proof
  apply StatMech.Walls.bc3_univ_closedUnderRho ω G

/--
[bc3_cluster_closedUnderRho](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_regionclosed.lean)
-/
@[path]
private lemma bc3_cluster_closedUnderRho_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {x : Site d} :
-- imply
  bc3_ClosedUnderRho ω G (cluster d (removeSite 0 (forceOpenFinset G ω)) x) := by
-- proof
  apply StatMech.Walls.bc3_cluster_closedUnderRho ω G x

/--
[bc3_cluster_closedUnderWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_regionclosed.lean)
-/
@[path]
private lemma bc3_cluster_closedUnderWiring_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {x : Site d} :
-- imply
  bc3_ClosedUnderWiring G (cluster d (removeSite 0 (forceOpenFinset G ω)) x) := by
-- proof
  apply StatMech.Walls.bc3_cluster_closedUnderWiring ω G x


-- created on 2026-10-23
