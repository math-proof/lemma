import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc3_rhoedgecases
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech StatMech.Walls


/--
[bc3_rhoEdge_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_rhoedgecases.lean)
-/
@[path]
private lemma bc3_rhoEdge_cases_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {e : Sym2 (Site d)}
-- given
  (h : removeSite 0 (forceOpenFinset G ω) e = true) :
-- imply
  (0 : Site d) ∉ e ∧ (ω e = true ∨ e ∈ G) := by
-- proof
  apply StatMech.Walls.bc3_rhoEdge_cases ω G h

/--
[bc3_rho_origin_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_rhoedgecases.lean)
-/
@[path]
private lemma bc3_rho_origin_notMem_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {e : Sym2 (Site d)}
-- given
  (h : removeSite 0 (forceOpenFinset G ω) e = true) :
-- imply
  (0 : Site d) ∉ e := by
-- proof
  apply StatMech.Walls.bc3_rho_origin_notMem ω G h

/--
[bc3_rho_endpoints_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_rhoedgecases.lean)
-/
@[path]
private lemma bc3_rho_endpoints_ne_zero_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {x y : Site d}
-- given
  (h : removeSite 0 (forceOpenFinset G ω) s(x, y) = true) :
-- imply
  x ≠ (0 : Site d) ∧ y ≠ (0 : Site d) := by
-- proof
  apply StatMech.Walls.bc3_rho_endpoints_ne_zero ω G h

/--
[bc3_rho_omegaOpen_or_forced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_rhoedgecases.lean)
-/
@[path]
private lemma bc3_rho_omegaOpen_or_forced_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {e : Sym2 (Site d)}
-- given
  (h : removeSite 0 (forceOpenFinset G ω) e = true) :
-- imply
  ω e = true ∨ e ∈ G := by
-- proof
  apply StatMech.Walls.bc3_rho_omegaOpen_or_forced ω G h

/--
[bc3_isOpenEdge_rho_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_rhoedgecases.lean)
-/
@[path]
private lemma bc3_isOpenEdge_rho_cases_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {x y : Site d}
-- given
  (h : IsOpenEdge d (removeSite 0 (forceOpenFinset G ω)) x y) :
-- imply
  (hypercubicLattice d).Adj x y ∧ (0 : Site d) ∉ s(x, y) ∧ (ω s(x, y) = true ∨ s(x, y) ∈ G) := by
-- proof
  apply StatMech.Walls.bc3_isOpenEdge_rho_cases ω G h

/--
[bc3_rho_openSubgraph_le_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_rhoedgecases.lean)
-/
@[path]
private lemma bc3_rho_openSubgraph_le_lattice_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))} :
-- imply
  openSubgraph d (removeSite 0 (forceOpenFinset G ω)) ≤ hypercubicLattice d := by
-- proof
  apply StatMech.Walls.bc3_rho_openSubgraph_le_lattice ω G

/--
[bc3_rho_edgeSet_subset_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_rhoedgecases.lean)
-/
@[path]
private lemma bc3_rho_edgeSet_subset_lattice_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))} :
-- imply
  (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).edgeSet ⊆ (hypercubicLattice d).edgeSet := by
-- proof
  apply StatMech.Walls.bc3_rho_edgeSet_subset_lattice ω G

/--
[bc3_rho_edgeSet_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_rhoedgecases.lean)
-/
@[path]
private lemma bc3_rho_edgeSet_cases_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {e : Sym2 (Site d)}
-- given
  (h : e ∈ (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).edgeSet) :
-- imply
  e ∈ (hypercubicLattice d).edgeSet ∧ (0 : Site d) ∉ e ∧ (ω e = true ∨ e ∈ G) := by
-- proof
  apply StatMech.Walls.bc3_rho_edgeSet_cases ω G h

/--
[bc3_isOpenEdge_rhoCorridor_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_rhoedgecases.lean)
-/
@[path]
private lemma bc3_isOpenEdge_rhoCorridor_cases_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j₁ j₂ j₃ : Fin d}
  {L₁ L₂ L₃ : ℕ}
  {x y : Site d}
-- given
  (h : IsOpenEdge d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪ hrHD_corridorEdges j₃ (L₃ + 1)) ω)) x y) :
-- imply
  (hypercubicLattice d).Adj x y ∧ (0 : Site d) ∉ s(x, y) ∧ (ω s(x, y) = true ∨ s(x, y) ∈ hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪ hrHD_corridorEdges j₃ (L₃ + 1)) := by
-- proof
  apply StatMech.Walls.bc3_isOpenEdge_rhoCorridor_cases ω j₁ j₂ j₃ L₁ L₂ L₃ h

/--
[bc3_rhoedgecases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_rhoedgecases.lean)
-/
@[path]
private lemma bc3_rhoedgecases_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {x y : Site d}
-- given
  (h : IsOpenEdge d (removeSite 0 (forceOpenFinset G ω)) x y) :
-- imply
  (hypercubicLattice d).Adj x y ∧ (0 : Site d) ∉ s(x, y) ∧ (ω s(x, y) = true ∨ s(x, y) ∈ G) := by
-- proof
  apply StatMech.Walls.bc3_rhoedgecases ω G h


-- created on 2026-10-23
