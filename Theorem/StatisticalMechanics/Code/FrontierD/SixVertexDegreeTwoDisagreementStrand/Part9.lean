/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentCType.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part5
import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part10
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexTorusEdgeSeamSign_eq_zero_or_one_or_neg_one
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (e : SixVertexTorusEdge T) :
    sixVertexTorusEdgeSeamSign omega eta e = 0 ∨
      sixVertexTorusEdgeSeamSign omega eta e = 1 ∨
      sixVertexTorusEdgeSeamSign omega eta e = -1 := by
  unfold sixVertexTorusEdgeSeamSign
  split
  · cases omega.vertical e.2 <;> cases eta.vertical e.2 <;> simp
  · simp

theorem sixVertexTorusEdgeSeamSign_eq_zero_of_not_disagrees
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (e : SixVertexTorusEdge T)
    (hagree : ¬ sixVertexTorusEdgeDisagrees omega eta e) :
    sixVertexTorusEdgeSeamSign omega eta e = 0 := by
  rcases e with ⟨dir, ⟨i, j⟩⟩
  fin_cases dir
  · simp [sixVertexTorusEdgeSeamSign]
  · simp [sixVertexTorusEdgeDisagrees, sixVertexTorusEdgeArrow] at hagree
    by_cases hj : j = svFinLast T.height_pos
    · subst j
      simp [sixVertexTorusEdgeSeamSign, ← hagree]
    · simp [sixVertexTorusEdgeSeamSign, hj]


theorem sum_sixVertexDisagreementEdge_seamSign
    {T : EvenTorus} (omega eta : SixVertexArrows T) :
    (∑ e : SixVertexDisagreementEdge omega eta,
        sixVertexTorusEdgeSeamSign omega eta e.1) =
      ∑ e : SixVertexTorusEdge T,
        sixVertexTorusEdgeSeamSign omega eta e := by
  classical
  rw [← Finset.sum_subtype
    (Finset.univ.filter fun e : SixVertexTorusEdge T =>
      sixVertexTorusEdgeDisagrees omega eta e) (by simp)
    (sixVertexTorusEdgeSeamSign omega eta), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hdis : sixVertexTorusEdgeDisagrees omega eta e
  · simp [hdis]
  · simp [hdis,
      sixVertexTorusEdgeSeamSign_eq_zero_of_not_disagrees omega eta e hdis]


theorem sum_sixVertexTorusEdge_seamSign_eq_fullTransfer
    {T : EvenTorus} (omega eta : SixVertexArrows T) :
    (∑ e : SixVertexTorusEdge T,
        sixVertexTorusEdgeSeamSign omega eta e) =
      sixVertexTorusMaskSeamTransfer
        (sixVertexFullDisagreementMask omega eta) omega eta := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  have hzero : (∑ y : T.Vertex,
      sixVertexTorusEdgeSeamSign omega eta (0, y)) = 0 := by
    simp [sixVertexTorusEdgeSeamSign]
  rw [hzero, zero_add, Fintype.sum_prod_type]
  have hinner (i : Fin T.width) :
      (∑ j : Fin T.height,
        sixVertexTorusEdgeSeamSign omega eta (1, (i, j))) =
        (eta.vertical (i, svFinLast T.height_pos)).toNat -
          (omega.vertical (i, svFinLast T.height_pos)).toNat := by
    rw [Finset.sum_eq_single (svFinLast T.height_pos)]
    · simp [sixVertexTorusEdgeSeamSign]
    · intro j hj hne
      simp [sixVertexTorusEdgeSeamSign, hne]
    · simp
  simp_rw [hinner]
  unfold sixVertexTorusMaskSeamTransfer
  apply Finset.sum_congr rfl
  intro i hi
  cases ho : omega.vertical (i, svFinLast T.height_pos) <;>
    cases he : eta.vertical (i, svFinLast T.height_pos) <;>
    simp [sixVertexFullDisagreementMask, ho, he]


end
end StatMech.FrontierD
