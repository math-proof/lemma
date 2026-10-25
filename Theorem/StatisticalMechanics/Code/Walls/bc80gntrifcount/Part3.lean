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
import Def.StatisticalMechanics.Code.Walls.bc80gntrifcount.Part3
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

theorem bc80_mem_gapSet (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)]
    (hyS : ∀ y ∈ bc73_fiber ω L R c, y ∈ S) (y : Site d) :
    y ∈ bc80_gapSet ω L R c S hyS ↔
      ∃ hy : y ∈ bc73_fiber ω L R c,
        (⟨y, hyS y hy⟩ : (↑S : Type)) ∉ bc80_branchFinset ω L R c S := by
  classical
  rw [bc80_gapSet, Finset.mem_filter]
  constructor
  · rintro ⟨hy, hcond⟩
    rw [dif_pos hy] at hcond
    exact ⟨hy, hcond⟩
  · rintro ⟨hy, hbr⟩
    exact ⟨hy, by rw [dif_pos hy]; exact hbr⟩

open Classical in


theorem bc80_coarseCount_le_branch_of_gap_empty (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)]
    (hyS : ∀ y ∈ bc73_fiber ω L R c, y ∈ S)
    (hgap : bc80_gapSet ω L R c S hyS = ∅) :
    (bc73_fiber ω L R c).card ≤ (bc80_branchFinset ω L R c S).card := by
  classical
  rcases (bc73_fiber ω L R c).eq_empty_or_nonempty with hemp | hne
  · rw [hemp]; simp
  · 
    haveI : Nonempty (↑S : Type) := ⟨⟨hne.choose, hyS hne.choose hne.choose_spec⟩⟩
    set ι : Site d → (↑S : Type) := fun y => if hy : y ∈ bc73_fiber ω L R c then ⟨y, hyS y hy⟩
      else Classical.arbitrary (↑S : Type) with hι
    refine Finset.card_le_card_of_injOn ι ?_ ?_
    · intro y hy
      have hy' : y ∈ bc73_fiber ω L R c := hy
      have hιeq : ι y = ⟨y, hyS y hy'⟩ := by simp only [hι, dif_pos hy']
      rw [hιeq]
      by_contra hbr
      have : y ∈ bc80_gapSet ω L R c S hyS :=
        (bc80_mem_gapSet ω L R c S hyS y).mpr ⟨hy', hbr⟩
      rw [hgap] at this; exact absurd this (Finset.notMem_empty y)
    · intro y hy z hz hyz
      have hy' : y ∈ bc73_fiber ω L R c := hy
      have hz' : z ∈ bc73_fiber ω L R c := hz
      have hιy : ι y = ⟨y, hyS y hy'⟩ := by simp only [hι, dif_pos hy']
      have hιz : ι z = ⟨z, hyS z hz'⟩ := by simp only [hι, dif_pos hz']
      rw [hιy, hιz] at hyz
      exact congrArg Subtype.val hyz


open Classical in


theorem bc80_upperLines_emptyFiber_fiber_bound {L R : ℕ} (hR : 1 ≤ R)
    (c : Fin 2 → Fin (2 * L + 1)) (hempty : bc73_fiber bc60_upperLines L R c = ∅) :
    (bc73_fiber bc60_upperLines L R c).card ≤ boxSV_boundaryCard 2 R :=
  bc80_fiber_le_boundary_via_branch bc60_upperLines L R c
    (bc75_upperLines_emptyFiber_gnTrifData hR c hempty)


theorem bc80_upperLines_ambient_coarseTrif {L : ℕ} (hL : 3 ≤ L) :
    bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) :=
  bc61_wholeBox_severs_upperLines hL


theorem bc80_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (c : Fin 2 → Fin (2 * L + 1))
      (S : Set (Site 2)) (_ : Fintype (↑S : Type)) (_ : Nonempty (↑S : Type)),
      (∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v) →
      (bc80_branchFinset ω L R c S).card ≤ (bc80_leafFinset ω L R c S).card) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (c : Fin 2 → Fin (2 * L + 1))
      (S : Set (Site 2)) (_ : Fintype (↑S : Type)) (_ : Nonempty (↑S : Type)),
      (∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v) →
      bc80_LeafBoundaryInj ω L R c S →
      bc80_GnTrifCount ω L R c S ≤ boxSV_boundaryCard 2 R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (c : Fin 2 → Fin (2 * L + 1)),
      bc75_FiberGnTrifData ω L R c → (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard 2 R) ∧
    
    (∀ {L : ℕ}, 3 ≤ L → bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω L R c S _ _ hmin
    exact bc80_branch_le_leaf ω L R c S (fun v => by convert hmin v using 2)
  · intro ω L R c S _ _ hmin hleaf
    exact bc80_GnTrifCount_le_boundary ω L R c S (fun v => by convert hmin v using 2) hleaf
  · intro ω L R c h; exact bc80_fiber_le_boundary_via_branch ω L R c h
  · intro L hL; exact bc80_upperLines_ambient_coarseTrif hL

end StatMech.Walls
