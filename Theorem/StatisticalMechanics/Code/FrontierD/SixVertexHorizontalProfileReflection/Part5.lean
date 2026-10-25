/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileSign
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHorizontalFalseForcedColumns_eq_compl_trueAllowed
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (completion : SixVertexVerticalCompletion T horizontal) :
    sixVertexHorizontalFalseForcedColumns horizontal =
      Finset.univ \ sixVertexHorizontalTrueAllowedColumns horizontal := by
  ext i
  simp only [sixVertexHorizontalFalseForcedColumns, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_sdiff,
    sixVertexHorizontalTrueAllowedColumns]
  constructor
  · rintro ⟨hfalse, hnotTrue⟩
    exact hnotTrue
  · intro hnotAllowed
    rcases sixVertexHorizontalColumnSeamAllowed_false_or_true completion i with
      hfalse | htrue
    · exact ⟨hfalse, hnotAllowed⟩
    · exact (hnotAllowed htrue).elim

theorem sixVertexVerticalCompletion_reflect
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (completion : SixVertexVerticalCompletion T horizontal) :
    Nonempty (SixVertexVerticalCompletion T
      (sixVertexReflectHorizontalField horizontal)) := by
  refine ⟨sixVertexVerticalCompletionOfColumns (fun i => ?_)⟩
  let k := finitePeriodicSucc T.width_pos
    (sixVertexCyclicNeg T.width_pos i)
  apply Classical.choice
  change Nonempty
    (SixVertexVerticalColumnCompletion T
      (sixVertexReflectHorizontalField horizontal) i)
  rcases sixVertexHorizontalColumnSeamAllowed_false_or_true
      completion k with hfalse | htrue
  · have hreflected :
        sixVertexHorizontalColumnSeamAllowed
          (sixVertexReflectHorizontalField horizontal) i true :=
      (sixVertexHorizontalColumnSeamAllowed_reflect_true_iff
        horizontal i).2 hfalse
    exact ⟨(Classical.choice hreflected).1⟩
  · have hreflected :
        sixVertexHorizontalColumnSeamAllowed
          (sixVertexReflectHorizontalField horizontal) i false :=
      (sixVertexHorizontalColumnSeamAllowed_reflect_false_iff
        horizontal i).2 htrue
    exact ⟨(Classical.choice hreflected).1⟩

theorem sixVertexVerticalCompletion_reflect_iff
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    Nonempty (SixVertexVerticalCompletion T
        (sixVertexReflectHorizontalField horizontal)) ↔
      Nonempty (SixVertexVerticalCompletion T horizontal) := by
  constructor
  · rintro ⟨completion⟩
    have hreflected := sixVertexVerticalCompletion_reflect completion
    have hfield :
        sixVertexReflectHorizontalField
            (sixVertexReflectHorizontalField horizontal) = horizontal := by
      funext v
      apply congrArg horizontal
      apply Prod.ext
      · exact sixVertexCyclicNeg_involutive T.width_pos v.1
      · rfl
    rw [hfield] at hreflected
    exact hreflected
  · rintro ⟨completion⟩
    exact sixVertexVerticalCompletion_reflect completion

theorem card_sixVertexHorizontalFreeColumns_reflect
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    (sixVertexHorizontalFreeColumns
        (sixVertexReflectHorizontalField horizontal)).card =
      (sixVertexHorizontalFreeColumns horizontal).card := by
  let xEquiv : Fin T.width ≃ Fin T.width :=
    (sixVertexCyclicNegEquiv T.width_pos).trans
      (svFinitePeriodicSuccEquiv T.width_pos)
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv xEquiv
  intro i
  change i ∈ sixVertexHorizontalFreeColumns
      (sixVertexReflectHorizontalField horizontal) ↔
    xEquiv i ∈ sixVertexHorizontalFreeColumns horizontal
  simp only [sixVertexHorizontalFreeColumns, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [← sixVertexHorizontalColumnSeamAllowed_both_iff_free,
    ← sixVertexHorizontalColumnSeamAllowed_both_iff_free]
  rw [sixVertexHorizontalColumnSeamAllowed_reflect_false_iff,
    sixVertexHorizontalColumnSeamAllowed_reflect_true_iff]
  change (_ ∧ _) ↔
    (sixVertexHorizontalColumnSeamAllowed horizontal
        (finitePeriodicSucc T.width_pos
          (sixVertexCyclicNeg T.width_pos i)) false ∧
      sixVertexHorizontalColumnSeamAllowed horizontal
        (finitePeriodicSucc T.width_pos
          (sixVertexCyclicNeg T.width_pos i)) true)
  tauto

theorem card_sixVertexHorizontalForcedTrueColumns_reflect
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    (sixVertexHorizontalForcedTrueColumns
        (sixVertexReflectHorizontalField horizontal)).card =
      (sixVertexHorizontalFalseForcedColumns horizontal).card := by
  let xEquiv : Fin T.width ≃ Fin T.width :=
    (sixVertexCyclicNegEquiv T.width_pos).trans
      (svFinitePeriodicSuccEquiv T.width_pos)
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv xEquiv
  intro i
  simp only [sixVertexHorizontalForcedTrueColumns, Finset.mem_filter,
    sixVertexHorizontalTrueAllowedColumns, Finset.mem_univ, true_and,
    sixVertexHorizontalFalseForcedColumns]
  rw [sixVertexHorizontalColumnSeamAllowed_reflect_true_iff,
    sixVertexHorizontalColumnSeamAllowed_reflect_false_iff]
  rfl

theorem card_sixVertexHorizontalFalseForcedColumns
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (completion : SixVertexVerticalCompletion T horizontal) :
    (sixVertexHorizontalFalseForcedColumns horizontal).card =
      T.width - (sixVertexHorizontalFreeColumns horizontal).card -
        (sixVertexHorizontalForcedTrueColumns horizontal).card := by
  rw [sixVertexHorizontalFalseForcedColumns_eq_compl_trueAllowed completion,
    Finset.card_sdiff]
  have hInter :
      sixVertexHorizontalTrueAllowedColumns horizontal ∩ Finset.univ =
        sixVertexHorizontalTrueAllowedColumns horizontal :=
    Finset.inter_univ _
  rw [hInter, Finset.card_univ, Fintype.card_fin]
  have hsplit := Finset.card_sdiff_add_card_eq_card
    (sixVertexHorizontalForcedTrueColumns_subset_trueAllowed horizontal)
  rw [sixVertexHorizontalTrueAllowed_sdiff_forced_eq_freeColumns] at hsplit
  omega

end
end StatMech.FrontierD
