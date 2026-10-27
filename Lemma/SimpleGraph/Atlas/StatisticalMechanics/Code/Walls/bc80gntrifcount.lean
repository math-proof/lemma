import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc80gntrifcount.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc80_branch_le_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc80gntrifcount.lean)
-/
@[path]
private lemma bc80_branch_le_leaf_eq
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
  apply StatMech.Walls.bc80_branch_le_leaf ω L R c S hmin

/--
[bc80_GnTrifCount_le_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc80gntrifcount.lean)
-/
@[path]
private lemma bc80_GnTrifCount_le_leaf_eq
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
  bc80_GnTrifCount ω L R c S ≤ (bc80_leafFinset ω L R c S).card := by
-- proof
  apply StatMech.Walls.bc80_GnTrifCount_le_leaf ω L R c S hmin

/--
[bc80_leaf_le_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc80gntrifcount.lean)
-/
@[path]
private lemma bc80_leaf_le_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {S : Set (Site d)}
  [Fintype (↑S : Type)]
-- given
  (hleaf : bc80_LeafBoundaryInj ω L R c S) :
-- imply
  (bc80_leafFinset ω L R c S).card ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc80_leaf_le_boundary ω L R c S hleaf

/--
[bc80_branch_le_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc80gntrifcount.lean)
-/
@[path]
private lemma bc80_branch_le_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {S : Set (Site d)}
  [Fintype (↑S : Type)]
  [Nonempty (↑S : Type)]
-- given
  (hmin : ∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v)
  (hleaf : bc80_LeafBoundaryInj ω L R c S) :
-- imply
  (bc80_branchFinset ω L R c S).card ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc80_branch_le_boundary ω L R c S hmin hleaf

/--
[bc80_GnTrifCount_le_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc80gntrifcount.lean)
-/
@[path]
private lemma bc80_GnTrifCount_le_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {S : Set (Site d)}
  [Fintype (↑S : Type)]
  [Nonempty (↑S : Type)]
-- given
  (hmin : ∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v)
  (hleaf : bc80_LeafBoundaryInj ω L R c S) :
-- imply
  bc80_GnTrifCount ω L R c S ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc80_GnTrifCount_le_boundary ω L R c S hmin hleaf

/--
[bc80_coarseTrif_mem_branch_of_gnCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc80gntrifcount.lean)
-/
@[path]
private lemma bc80_coarseTrif_mem_branch_of_gnCut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {y : Site d}
  {S : Set (Site d)}
  [Fintype (↑S : Type)]
  {v₁ v₂ v₃ : (↑S : Type)}
-- given
  (hyS : y ∈ S)
  (hadj₁ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS⟩ v₁)
  (hadj₂ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS⟩ v₂)
  (hadj₃ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS⟩ v₃)
  (hcut₁₂ : ¬ ((bc75_fiberQuotBox ω L R c S).induce ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable ⟨v₁, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₁).symm⟩ ⟨v₂, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₂).symm⟩)
  (hcut₁₃ : ¬ ((bc75_fiberQuotBox ω L R c S).induce ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable ⟨v₁, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₁).symm⟩ ⟨v₃, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₃).symm⟩)
  (hcut₂₃ : ¬ ((bc75_fiberQuotBox ω L R c S).induce ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable ⟨v₂, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₂).symm⟩ ⟨v₃, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₃).symm⟩) :
-- imply
  (⟨y, hyS⟩ : (↑S : Type)) ∈ bc80_branchFinset ω L R c S := by
-- proof
  apply StatMech.Walls.bc80_coarseTrif_mem_branch_of_gnCut ω L R c S hyS hadj₁ hadj₂ hadj₃ hcut₁₂ hcut₁₃ hcut₂₃

/--
[bc80_coarseCount_le_branch_on_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc80gntrifcount.lean)
-/
@[path]
private lemma bc80_coarseCount_le_branch_on_carrier_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {S : Set (Site d)}
  [Fintype (↑S : Type)]
  [Nonempty (↑S : Type)]
-- given
  (hyS : ∀ y ∈ bc73_fiber ω L R c, y ∈ S)
  (htriData : ∀ y (hy : y ∈ bc73_fiber ω L R c), ∃ (v₁ v₂ v₃ : (↑S : Type)) (h₁ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS y hy⟩ v₁) (h₂ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS y hy⟩ v₂) (h₃ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS y hy⟩ v₃), ¬ (((bc75_fiberQuotBox ω L R c S).induce ({(⟨y, hyS y hy⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable ⟨v₁, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₁).symm⟩ ⟨v₂, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₂).symm⟩) ∧ ¬ (((bc75_fiberQuotBox ω L R c S).induce ({(⟨y, hyS y hy⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable ⟨v₁, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₁).symm⟩ ⟨v₃, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₃).symm⟩) ∧ ¬ (((bc75_fiberQuotBox ω L R c S).induce ({(⟨y, hyS y hy⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable ⟨v₂, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₂).symm⟩ ⟨v₃, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₃).symm⟩)) :
-- imply
  (bc73_fiber ω L R c).card ≤ (bc80_branchFinset ω L R c S).card := by
-- proof
  apply StatMech.Walls.bc80_coarseCount_le_branch_on_carrier ω L R c S hyS htriData

/--
[bc80_coarseCount_le_branch_of_gnData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc80gntrifcount.lean)
-/
@[path]
private lemma bc80_coarseCount_le_branch_of_gnData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
-- given
  (h : bc75_FiberGnTrifData ω L R c) :
-- imply
  ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)), (bc73_fiber ω L R c).card ≤ (bc80_branchFinset ω L R c S).card := by
-- proof
  apply StatMech.Walls.bc80_coarseCount_le_branch_of_gnData ω L R c h

/--
[bc80_leafBoundaryInj_of_gnData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc80gntrifcount.lean)
-/
@[path]
private lemma bc80_leafBoundaryInj_of_gnData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {S : Set (Site d)}
  [Fintype (↑S : Type)]
-- given
  (hleafmap : ∀ v : (↑S : Type), (bc75_spanForest ω L R c S).degree v = 1 → (v : Site d) ∈ vertexBoundary d R) :
-- imply
  bc80_LeafBoundaryInj ω L R c S := by
-- proof
  apply StatMech.Walls.bc80_leafBoundaryInj_of_gnData ω L R c S hleafmap

/--
[bc80_fiber_le_boundary_via_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc80gntrifcount.lean)
-/
@[path]
private lemma bc80_fiber_le_boundary_via_branch_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
-- given
  (h : bc75_FiberGnTrifData ω L R c) :
-- imply
  (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc80_fiber_le_boundary_via_branch ω L R c h

/--
[bc80_mem_gapSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc80gntrifcount.lean)
-/
@[path]
private lemma bc80_mem_gapSet_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {S : Set (Site d)}
  [Fintype (↑S : Type)]
  {y : Site d}
-- given
  (hyS : ∀ y ∈ bc73_fiber ω L R c, y ∈ S) :
-- imply
  y ∈ bc80_gapSet ω L R c S hyS ↔ ∃ hy : y ∈ bc73_fiber ω L R c, (⟨y, hyS y hy⟩ : (↑S : Type)) ∉ bc80_branchFinset ω L R c S := by
-- proof
  apply StatMech.Walls.bc80_mem_gapSet ω L R c S hyS y

/--
[bc80_coarseCount_le_branch_of_gap_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc80gntrifcount.lean)
-/
@[path]
private lemma bc80_coarseCount_le_branch_of_gap_empty_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {S : Set (Site d)}
  [Fintype (↑S : Type)]
-- given
  (hyS : ∀ y ∈ bc73_fiber ω L R c, y ∈ S)
  (hgap : bc80_gapSet ω L R c S hyS = ∅) :
-- imply
  (bc73_fiber ω L R c).card ≤ (bc80_branchFinset ω L R c S).card := by
-- proof
  apply StatMech.Walls.bc80_coarseCount_le_branch_of_gap_empty ω L R c S hyS hgap

/--
[bc80_upperLines_emptyFiber_fiber_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc80gntrifcount.lean)
-/
@[path]
private lemma bc80_upperLines_emptyFiber_fiber_bound_eq
  {d : ℕ}
  {L R : ℕ}
  {c : Fin 2 → Fin (2 * L + 1)}
-- given
  (hR : 1 ≤ R)
  (hempty : bc73_fiber bc60_upperLines L R c = ∅) :
-- imply
  (bc73_fiber bc60_upperLines L R c).card ≤ boxSV_boundaryCard 2 R := by
-- proof
  apply StatMech.Walls.bc80_upperLines_emptyFiber_fiber_bound hR c hempty

/--
[bc80_upperLines_ambient_coarseTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc80gntrifcount.lean)
-/
@[path]
private lemma bc80_upperLines_ambient_coarseTrif_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) := by
-- proof
  apply StatMech.Walls.bc80_upperLines_ambient_coarseTrif hL

/--
[bc80_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc80gntrifcount.lean)
-/
@[path]
private lemma bc80_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (c : Fin 2 → Fin (2 * L + 1)) (S : Set (Site 2)) (_ : Fintype (↑S : Type)) (_ : Nonempty (↑S : Type)), (∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v) → (bc80_branchFinset ω L R c S).card ≤ (bc80_leafFinset ω L R c S).card) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (c : Fin 2 → Fin (2 * L + 1)) (S : Set (Site 2)) (_ : Fintype (↑S : Type)) (_ : Nonempty (↑S : Type)), (∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v) → bc80_LeafBoundaryInj ω L R c S → bc80_GnTrifCount ω L R c S ≤ boxSV_boundaryCard 2 R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (c : Fin 2 → Fin (2 * L + 1)), bc75_FiberGnTrifData ω L R c → (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard 2 R) ∧ (∀ {L : ℕ}, 3 ≤ L → bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2)) := by
-- proof
  apply StatMech.Walls.bc80_status


-- created on 2026-10-23
