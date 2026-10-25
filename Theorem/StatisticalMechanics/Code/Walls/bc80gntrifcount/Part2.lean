/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc80gntrifcount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc75spanningtree.Part4
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
import Def.StatisticalMechanics.Code.Walls.bc80gntrifcount.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


open Classical in


theorem bc80_leaf_le_boundary (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)]
    (hleaf : bc80_LeafBoundaryInj ω L R c S) :
    (bc80_leafFinset ω L R c S).card ≤ boxSV_boundaryCard d R := by
  classical
  obtain ⟨lamL, hmap, hinj⟩ := hleaf
  have hkey := flc2_leaf_card_le_boundary (bc75_spanForest ω L R c S) R lamL hmap hinj
  simpa only [bc80_leafFinset] using hkey

open Classical in


theorem bc80_branch_le_boundary (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)] [Nonempty (↑S : Type)]
    (hmin : ∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v)
    (hleaf : bc80_LeafBoundaryInj ω L R c S) :
    (bc80_branchFinset ω L R c S).card ≤ boxSV_boundaryCard d R :=
  le_trans (bc80_branch_le_leaf ω L R c S hmin) (bc80_leaf_le_boundary ω L R c S hleaf)

open Classical in


theorem bc80_GnTrifCount_le_boundary (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)] [Nonempty (↑S : Type)]
    (hmin : ∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v)
    (hleaf : bc80_LeafBoundaryInj ω L R c S) :
    bc80_GnTrifCount ω L R c S ≤ boxSV_boundaryCard d R :=
  bc80_branch_le_boundary ω L R c S hmin hleaf


open Classical in


theorem bc80_coarseTrif_mem_branch_of_gnCut (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) {y : Site d} (S : Set (Site d)) [Fintype (↑S : Type)]
    (hyS : y ∈ S) {v₁ v₂ v₃ : (↑S : Type)}
    (hadj₁ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS⟩ v₁)
    (hadj₂ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS⟩ v₂)
    (hadj₃ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS⟩ v₃)
    (hcut₁₂ : ¬ ((bc75_fiberQuotBox ω L R c S).induce
        ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
      ⟨v₁, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₁).symm⟩
      ⟨v₂, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₂).symm⟩)
    (hcut₁₃ : ¬ ((bc75_fiberQuotBox ω L R c S).induce
        ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
      ⟨v₁, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₁).symm⟩
      ⟨v₃, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₃).symm⟩)
    (hcut₂₃ : ¬ ((bc75_fiberQuotBox ω L R c S).induce
        ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
      ⟨v₂, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₂).symm⟩
      ⟨v₃, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₃).symm⟩) :
    (⟨y, hyS⟩ : (↑S : Type)) ∈ bc80_branchFinset ω L R c S := by
  classical
  rw [bc80_branchFinset, Finset.mem_filter]
  exact ⟨Finset.mem_univ _,
    bc75_deg3_in_spanForest_of_gnCut ω L R c hyS hadj₁ hadj₂ hadj₃ hcut₁₂ hcut₁₃ hcut₂₃⟩


open Classical in


theorem bc80_coarseCount_le_branch_on_carrier (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)] [Nonempty (↑S : Type)]
    (hyS : ∀ y ∈ bc73_fiber ω L R c, y ∈ S)
    (htriData : ∀ y (hy : y ∈ bc73_fiber ω L R c),
      ∃ (v₁ v₂ v₃ : (↑S : Type))
        (h₁ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS y hy⟩ v₁)
        (h₂ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS y hy⟩ v₂)
        (h₃ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS y hy⟩ v₃),
        ¬ (((bc75_fiberQuotBox ω L R c S).induce
              ({(⟨y, hyS y hy⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
            ⟨v₁, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₁).symm⟩
            ⟨v₂, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₂).symm⟩) ∧
        ¬ (((bc75_fiberQuotBox ω L R c S).induce
              ({(⟨y, hyS y hy⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
            ⟨v₁, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₁).symm⟩
            ⟨v₃, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₃).symm⟩) ∧
        ¬ (((bc75_fiberQuotBox ω L R c S).induce
              ({(⟨y, hyS y hy⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
            ⟨v₂, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₂).symm⟩
            ⟨v₃, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj h₃).symm⟩)) :
    (bc73_fiber ω L R c).card ≤ (bc80_branchFinset ω L R c S).card := by
  classical
  
  set ι : Site d → (↑S : Type) := fun y => if hy : y ∈ bc73_fiber ω L R c then ⟨y, hyS y hy⟩
    else Classical.arbitrary (↑S : Type) with hι
  refine Finset.card_le_card_of_injOn ι ?_ ?_
  · 
    intro y hy
    have hy' : y ∈ bc73_fiber ω L R c := hy
    have hιeq : ι y = ⟨y, hyS y hy'⟩ := by simp only [hι, dif_pos hy']
    rw [hιeq]
    obtain ⟨v₁, v₂, v₃, h₁, h₂, h₃, hc₁₂, hc₁₃, hc₂₃⟩ := htriData y hy'
    exact bc80_coarseTrif_mem_branch_of_gnCut ω L R c S (hyS y hy') h₁ h₂ h₃ hc₁₂ hc₁₃ hc₂₃
  · 
    intro y hy z hz hyz
    have hy' : y ∈ bc73_fiber ω L R c := hy
    have hz' : z ∈ bc73_fiber ω L R c := hz
    have hιy : ι y = ⟨y, hyS y hy'⟩ := by simp only [hι, dif_pos hy']
    have hιz : ι z = ⟨z, hyS z hz'⟩ := by simp only [hι, dif_pos hz']
    rw [hιy, hιz] at hyz
    exact congrArg Subtype.val hyz

open Classical in


theorem bc80_coarseCount_le_branch_of_gnData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (h : bc75_FiberGnTrifData ω L R c) :
    ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)),
      (bc73_fiber ω L R c).card ≤ (bc80_branchFinset ω L R c S).card := by
  classical
  obtain ⟨S, hSfin, hSne, hyS, htriData, hmin, hleaf⟩ := h
  haveI : Nonempty (↑S : Type) := hSne
  exact ⟨S, hSfin, bc80_coarseCount_le_branch_on_carrier ω L R c S hyS htriData⟩


open Classical in


theorem bc80_leafBoundaryInj_of_gnData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)]
    (hleafmap : ∀ v : (↑S : Type),
      (bc75_spanForest ω L R c S).degree v = 1 → (v : Site d) ∈ vertexBoundary d R) :
    bc80_LeafBoundaryInj ω L R c S := by
  classical
  refine ⟨Subtype.val, hleafmap, ?_⟩
  intro a _ b _ hab
  exact Subtype.ext hab

open Classical in


theorem bc80_fiber_le_boundary_via_branch (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (h : bc75_FiberGnTrifData ω L R c) :
    (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard d R := by
  classical
  
  obtain ⟨S, hSfin, hSne, hyS, htriData, hmin, hleafmap⟩ := h
  haveI : Nonempty (↑S : Type) := hSne
  
  have hfb : (bc73_fiber ω L R c).card ≤ (bc80_branchFinset ω L R c S).card :=
    bc80_coarseCount_le_branch_on_carrier ω L R c S hyS htriData
  
  have hbb : (bc80_branchFinset ω L R c S).card ≤ boxSV_boundaryCard d R :=
    bc80_branch_le_boundary ω L R c S hmin (bc80_leafBoundaryInj_of_gnData ω L R c S hleafmap)
  exact le_trans hfb hbb


end StatMech.Walls
