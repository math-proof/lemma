/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRowDataRepairRelation.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorMaskMatching.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamRowDataMaskHall.Part2
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem rowDataRepairHall_iff_maskwise
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W) :
    RowDataRepairHall ends m j k l zero ↔
      forall p : Finset I × Finset I,
        Fintype.card (leftMaskFiber ends m j k l zero p) <=
          Fintype.card (rightMaskFiber ends m j k l zero p) := by
  constructor
  · intro hhall
    have hhall' : forall S : Finset (leftRowData ends m j k l zero),
        S.card <= (Finset.univ.filter fun e =>
          ∃ d ∈ S, RowDataRepairRelated ends m j k l zero d e).card := by
      simpa [RowDataRepairHall, admissibleRightRowNeighborhood] using hhall
    obtain ⟨g, hg, hrelated⟩ :=
      (Fintype.all_card_le_filter_rel_iff_exists_injective
        (RowDataRepairRelated ends m j k l zero)).1 hhall'
    let f := maskFiberEmbeddings_of_related_injection
      ends m j k l zero g hg hrelated
    intro p
    exact Fintype.card_le_of_injective (f p) (f p).injective
  · exact rowDataRepairHall_of_maskwise ends m j k l zero


theorem rowDataRepairHall_of_subsingleton_leftMaskFibers
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : forall i, i ∈ m -> ¬(ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hsub : forall p : Finset I × Finset I,
      Subsingleton (leftMaskFiber ends m j k l zero p)) :
    RowDataRepairHall ends m j k l zero := by
  apply rowDataRepairHall_of_maskFiberEmbeddings
  intro p
  by_cases hleft : Nonempty (leftMaskFiber ends m j k l zero p)
  · let c := Classical.choice hleft
    let d := Classical.choice
      (rightMaskFiber_nonempty_of_left hloop hjk hkl hk0 p c)
    letI : Subsingleton (leftMaskFiber ends m j k l zero p) := hsub p
    exact
      { toFun := fun _ => d
        inj' := fun a b _ => Subsingleton.elim a b }
  · exact
      { toFun := fun c => False.elim (hleft ⟨c⟩)
        inj' := fun a _ _ => False.elim (hleft ⟨a⟩) }


theorem rowDataRepairHall_of_subsingleton_cycleSectors
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : forall i, i ∈ m -> ¬(ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hcycle : forall p : Finset I × Finset I,
      Subsingleton (boundarySector ends p.1 ∅) ∧
        Subsingleton (boundarySector ends p.2 ∅)) :
    RowDataRepairHall ends m j k l zero := by
  apply rowDataRepairHall_of_subsingleton_leftMaskFibers
    ends m j k l zero hloop hjk hkl hk0
  intro p
  exact subsingleton_leftMaskFiber_of_cycleSectors
    ends m j k l zero p (hcycle p).1 (hcycle p).2

end StatMech.GrahamGHS.FourColor
