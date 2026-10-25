import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc84leafboundary
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc84_peeling_forest_le_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc84leafboundary.lean)
-/
@[path]
private lemma bc84_peeling_forest_le_boundary_eq
  {d : ℕ}
  [Fintype W]
  [Nonempty W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {R : ℕ}
  {lam : W → Site d}
-- given
  (hacyc : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v)
  (hmap : ∀ v, G.degree v = 1 → lam v ∈ vertexBoundary d R)
  (hinj : Set.InjOn lam (univ.filter (fun v => G.degree v = 1))) :
-- imply
  (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc84_peeling_forest_le_boundary G R hacyc hmin lam hmap hinj

/--
[bc84_leafBoundaryInj_of_boundaryLeaves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc84leafboundary.lean)
-/
@[path]
private lemma bc84_leafBoundaryInj_of_boundaryLeaves_eq
  {d : ℕ}
  {S : Set (Site d)}
  [Fintype (↑S : Type)]
  {H : SimpleGraph (↑S : Type)}
  [DecidableRel H.Adj]
  {R : ℕ}
-- given
  (hleafmap : ∀ v : (↑S : Type), H.degree v = 1 → (v : Site d) ∈ vertexBoundary d R) :
-- imply
  (∀ v : (↑S : Type), H.degree v = 1 → (Subtype.val v) ∈ vertexBoundary d R) ∧ Set.InjOn Subtype.val (↑(Finset.univ.filter (fun v => H.degree v = 1)) : Set (↑S : Type)) := by
-- proof
  apply StatMech.Walls.bc84_leafBoundaryInj_of_boundaryLeaves S H R hleafmap

/--
[bc84_fiber_bound_of_assembled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc84leafboundary.lean)
-/
@[path]
private lemma bc84_fiber_bound_of_assembled_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {S : Set (Site d)}
  [Fintype (↑S : Type)]
  [Nonempty (↑S : Type)]
  {H : SimpleGraph (↑S : Type)}
  [DecidableRel H.Adj]
-- given
  (hyS : ∀ y ∈ bc73_fiber ω L R c, y ∈ S)
  (hacyc : H.IsAcyclic)
  (hmin : ∀ v : (↑S : Type), 1 ≤ H.degree v)
  (hdeg3 : ∀ y (hy : y ∈ bc73_fiber ω L R c), 3 ≤ H.degree ⟨y, hyS y hy⟩)
  (hleafmap : ∀ v : (↑S : Type), H.degree v = 1 → (v : Site d) ∈ vertexBoundary d R) :
-- imply
  (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc84_fiber_bound_of_assembled ω L R c S H hyS hacyc hmin hdeg3 hleafmap

/--
[bc84_gnTrifData_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc84leafboundary.lean)
-/
@[path]
private lemma bc84_gnTrifData_components_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
-- given
  (h : bc75_FiberGnTrifData ω L R c) :
-- imply
  ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (_ : Nonempty (↑S : Type)) (hyS : ∀ y ∈ bc73_fiber ω L R c, y ∈ S), (bc75_spanForest ω L R c S).IsAcyclic ∧ (∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v) ∧ (∀ y (hy : y ∈ bc73_fiber ω L R c), 3 ≤ (bc75_spanForest ω L R c S).degree ⟨y, hyS y hy⟩) ∧ (∀ v : (↑S : Type), (bc75_spanForest ω L R c S).degree v = 1 → (v : Site d) ∈ vertexBoundary d R) := by
-- proof
  apply StatMech.Walls.bc84_gnTrifData_components ω L R c h

/--
[bc84_fiber_bound_of_gnTrifData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc84leafboundary.lean)
-/
@[path]
private lemma bc84_fiber_bound_of_gnTrifData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
-- given
  (h : bc75_FiberGnTrifData ω L R c) :
-- imply
  (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc84_fiber_bound_of_gnTrifData ω L R c h

/--
[bc84_leaf_boundary_is_perConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc84leafboundary.lean)
-/
@[path]
private lemma bc84_leaf_boundary_is_perConfig_eq
  {d : ℕ}
  [Fintype W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {R : ℕ}
  {lam : W → Site d}
-- given
  (hmap : ∀ v, G.degree v = 1 → lam v ∈ vertexBoundary d R)
  (hinj : Set.InjOn lam (univ.filter (fun v => G.degree v = 1))) :
-- imply
  (univ.filter (fun v => G.degree v = 1)).card ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc84_leaf_boundary_is_perConfig G R lam hmap hinj

/--
[bc84_upperLines_obstruction_is_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc84leafboundary.lean)
-/
@[path]
private lemma bc84_upperLines_obstruction_is_cut_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) ∧ Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc76_yBuf L)) ∧ ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ := by
-- proof
  apply StatMech.Walls.bc84_upperLines_obstruction_is_cut hL

/--
[bc84_upperLines_coarseTrif_and_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc84leafboundary.lean)
-/
@[path]
private lemma bc84_upperLines_coarseTrif_and_top_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) ∧ numInfiniteClusters 2 bc60_upperLines = ⊤ := by
-- proof
  apply StatMech.Walls.bc84_upperLines_coarseTrif_and_top hL

/--
[bc84_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc84leafboundary.lean)
-/
@[path]
private lemma bc84_status_eq
  {d : ℕ} :
-- imply
  (∀ (W : Type) (_ : Fintype W) (_ : Nonempty W) (G : SimpleGraph W) (_ : DecidableRel G.Adj) (R : ℕ) (lam : W → Site 2), G.IsAcyclic → (∀ v, 1 ≤ G.degree v) → (∀ v, G.degree v = 1 → lam v ∈ vertexBoundary 2 R) → Set.InjOn lam (univ.filter (fun v => G.degree v = 1)) → (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ boxSV_boundaryCard 2 R) ∧ (∀ (W : Type) (_ : Fintype W) (G : SimpleGraph W) (_ : DecidableRel G.Adj) (R : ℕ) (lam : W → Site 2), (∀ v, G.degree v = 1 → lam v ∈ vertexBoundary 2 R) → Set.InjOn lam (univ.filter (fun v => G.degree v = 1)) → (univ.filter (fun v => G.degree v = 1)).card ≤ boxSV_boundaryCard 2 R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (c : Fin 2 → Fin (2 * L + 1)), bc75_FiberGnTrifData ω L R c → (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard 2 R) ∧ (∀ {L : ℕ}, 3 ≤ L → ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩) := by
-- proof
  apply StatMech.Walls.bc84_status


-- created on 2026-10-23
