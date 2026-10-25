/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataRepairRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamComponentExchangeWeightedCounterexample.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorUniformMaskSelector.Part4
import Def.StatisticalMechanics.Code.FrontierA.GrahamRowDataRepairRelation.Part4
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem rowDataRepairHall_of_related_embedding
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (f : leftRowData ends m j k l zero ↪
      rightRowData ends m j k l zero)
    (hrelated : ∀ d, RowDataRepairRelated ends m j k l zero d (f d)) :
    RowDataRepairHall ends m j k l zero := by
  intro S
  calc
    S.card = (S.map f).card := (Finset.card_map f).symm
    _ ≤ (admissibleRightRowNeighborhood ends m j k l zero S).card := by
      apply Finset.card_le_card
      intro e he
      rcases Finset.mem_map.mp he with ⟨d, hd, hde⟩
      rw [mem_admissibleRightRowNeighborhood_iff]
      refine ⟨d, hd, ?_⟩
      rw [← hde]
      exact hrelated d


theorem GrahamWeightedRowMinor_of_rowDataRepairHall
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hhall : RowDataRepairHall ends m j k l zero) :
    GrahamWeightedRowMinor ends m j k l zero := by
  unfold GrahamWeightedRowMinor
  rw [← leftRowData_card_eq_weightedSum,
    ← rightRowData_card_eq_weightedSum]
  rw [← Finset.card_univ, ← Finset.card_univ]
  calc
    (Finset.univ : Finset (leftRowData ends m j k l zero)).card ≤
        (admissibleRightRowNeighborhood ends m j k l zero Finset.univ).card :=
      hhall Finset.univ
    _ ≤ (Finset.univ : Finset (rightRowData ends m j k l zero)).card :=
      Finset.card_le_card (Finset.subset_univ _)

end StatMech.GrahamGHS.FourColor
