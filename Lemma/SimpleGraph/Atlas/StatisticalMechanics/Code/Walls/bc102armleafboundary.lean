import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc102armleafboundary
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc102_count_forest_derivable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc102armleafboundary.lean)
-/
@[path]
private lemma bc102_count_forest_derivable_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc69_Gn_globalForest ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc102_count_forest_derivable ω L R h

/--
[bc102_bc64_gives_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc102armleafboundary.lean)
-/
@[path]
private lemma bc102_bc64_gives_count_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁)
  (hinj : bc64_CoarseBoundaryInjection ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc102_bc64_gives_count ω L R hz₀ hz₁ hzne hinj

/--
[bc102_bc64_gives_connectedForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc102armleafboundary.lean)
-/
@[path]
private lemma bc102_bc64_gives_connectedForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁)
  (hinj : bc64_CoarseBoundaryInjection ω L R) :
-- imply
  bc65_ConnectedCoarseForest ω L R := by
-- proof
  apply StatMech.Walls.bc102_bc64_gives_connectedForest ω L R hz₀ hz₁ hzne hinj

/--
[bc102_leaf_count_absorbs_shared](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc102armleafboundary.lean)
-/
@[path]
private lemma bc102_leaf_count_absorbs_shared_eq
  {d : ℕ}
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hacyc : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v) :
-- imply
  (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card := by
-- proof
  apply StatMech.Walls.bc102_leaf_count_absorbs_shared G hacyc hmin

/--
[bc102_leaf_boundary_free_on_subtype](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc102armleafboundary.lean)
-/
@[path]
private lemma bc102_leaf_boundary_free_on_subtype_eq
  {d : ℕ}
  {p : Site d → Prop}
  {S : Set (Subtype p)} :
-- imply
  Set.InjOn (Subtype.val : Subtype p → Site d) S := by
-- proof
  apply StatMech.Walls.bc102_leaf_boundary_free_on_subtype S

/--
[bc102_spanForest_branch_le_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc102armleafboundary.lean)
-/
@[path]
private lemma bc102_spanForest_branch_le_leaf_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {S : Set (Site d)}
  [Fintype (↑S : Type)]
  [Nonempty (↑S : Type)]
-- given
  (hmin : ∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v) :
-- imply
  (bc80_branchFinset ω L R c S).card ≤ (bc80_leafFinset ω L R c S).card := by
-- proof
  apply StatMech.Walls.bc102_spanForest_branch_le_leaf ω L R c S hmin

/--
[bc102_bc64_crossSV_refuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc102armleafboundary.lean)
-/
@[path]
private lemma bc102_bc64_crossSV_refuted_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧ Connected 2 bc60_upperLines (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) := by
-- proof
  apply StatMech.Walls.bc102_bc64_crossSV_refuted L

/--
[bc102_bc64_disjointStar_degrees](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc102armleafboundary.lean)
-/
@[path]
private lemma bc102_bc64_disjointStar_degrees_eq
  {d : ℕ} :
-- imply
  bc64_starG.degree 0 = 3 ∧ (∀ i : Fin 4, i ≠ 0 → bc64_starG.degree i = 1) := by
-- proof
  apply StatMech.Walls.bc102_bc64_disjointStar_degrees

/--
[bc102_BK_count_reduces_to_connectedForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc102armleafboundary.lean)
-/
@[path]
private lemma bc102_BK_count_reduces_to_connectedForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ} :
-- imply
  (bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) ∧ (∀ {z₀ z₁ : Site d}, z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ → bc64_CoarseBoundaryInjection ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
-- proof
  apply StatMech.Walls.bc102_BK_count_reduces_to_connectedForest ω L R

/--
[bc102_connectedForest_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc102armleafboundary.lean)
-/
@[path]
private lemma bc102_connectedForest_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁)
  (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bc102_connectedForest_of_noTrif ω L R hz₀ hz₁ hzne hno

/--
[bc102_upperLines_count_via_connectedForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc102armleafboundary.lean)
-/
@[path]
private lemma bc102_upperLines_count_via_connectedForest_eq
  {d : ℕ}
  {L R : ℕ}
-- given
  (h : bc69_Gn_globalForest bc60_upperLines L R) :
-- imply
  bc61_coarseTcount bc60_upperLines L R ≤ boxSV_boundaryCard 2 R := by
-- proof
  apply StatMech.Walls.bc102_upperLines_count_via_connectedForest h

/--
[bc102_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc102armleafboundary.lean)
-/
@[path]
private lemma bc102_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) ∧ (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [_inst : DecidableRel G.Adj], G.IsAcyclic → (∀ v, 1 ≤ G.degree v) → (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card) ∧ (bc64_starG.degree 0 = 3 ∧ (∀ i : Fin 4, i ≠ 0 → bc64_starG.degree i = 1)) ∧ (∀ (L : ℕ), Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧ Connected 2 bc60_upperLines (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d), z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ → bc64_CoarseBoundaryInjection ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
-- proof
  apply StatMech.Walls.bc102_status


-- created on 2026-10-23
