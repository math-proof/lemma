/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc74disjointforest.Part2
import Theorem.StatisticalMechanics.Code.Percolation.OpenSpanningForestClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SingleLeafHallClose.Part2
import Def.StatisticalMechanics.Code.Walls.bc75spanningtree
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


theorem bc75_collapseFiber_eq {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {c : Fin d → Fin (2 * L + 1)} {x y : Site d}
    (hy : y ∈ bc73_fiber ω L R c) (hx : x ∈ bc61_boxAround d L y) :
    bc75_collapseFiber ω L R c x = y := by
  classical
  have hex : ∃ y' ∈ bc73_fiber ω L R c, x ∈ bc61_boxAround d L y' := ⟨y, hy, hx⟩
  unfold bc75_collapseFiber
  rw [dif_pos hex]
  
  obtain ⟨hzmem, hzx⟩ := hex.choose_spec
  by_contra hne
  exact Finset.disjoint_left.mp
    (bc73_fiber_pairwise_disjoint ω L R c hzmem hy hne) hzx hx


theorem bc75_collapseFiber_id {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {c : Fin d → Fin (2 * L + 1)} {x : Site d}
    (hx : ∀ y ∈ bc73_fiber ω L R c, x ∉ bc61_boxAround d L y) :
    bc75_collapseFiber ω L R c x = x := by
  classical
  unfold bc75_collapseFiber
  rw [dif_neg]
  rintro ⟨y, hy, hxy⟩
  exact hx y hy hxy


theorem bc75_collapseFiber_center {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {c : Fin d → Fin (2 * L + 1)} {y : Site d} (hy : y ∈ bc73_fiber ω L R c) :
    bc75_collapseFiber ω L R c y = y :=
  bc75_collapseFiber_eq hy (bc72_y_mem_box L y)


theorem bc75_collapseFiber_mem_box_of_eq_center {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {c : Fin d → Fin (2 * L + 1)} {x y : Site d} (hy : y ∈ bc73_fiber ω L R c)
    (hxy : bc75_collapseFiber ω L R c x = y) :
    x ∈ bc61_boxAround d L y := by
  classical
  by_cases hex : ∃ y' ∈ bc73_fiber ω L R c, x ∈ bc61_boxAround d L y'
  · 
    obtain ⟨hzmem, hzx⟩ := hex.choose_spec
    have : bc75_collapseFiber ω L R c x = hex.choose := by
      unfold bc75_collapseFiber; rw [dif_pos hex]
    rw [this] at hxy
    rw [← hxy]; exact hzx
  · 
    have hex' : ∀ y' ∈ bc73_fiber ω L R c, x ∉ bc61_boxAround d L y' := by
      intro y' hy' hxy'; exact hex ⟨y', hy', hxy'⟩
    have hxx : bc75_collapseFiber ω L R c x = x := bc75_collapseFiber_id hex'
    rw [hxx] at hxy; rw [hxy]; exact bc72_y_mem_box L y


end StatMech.Walls
