/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoComponentStrand.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentBooleanOrbit.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitStrandPhysicalTarget
import Mathlib.Data.Finset.SymmDiff
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoComponentStrand
open Finset SimpleGraph
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexLocallyDegreeTwo.pairSwitch
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    SixVertexLocallyDegreeTwo
      (sixVertexTorusSwitchFirst mask omega eta)
      (sixVertexTorusSwitchSecond mask omega eta) := by
  intro vertex
  have hsides : sixVertexLocalDisagreementSides
        (sixVertexLocalIncomingPattern
          (sixVertexTorusSwitchFirst mask omega eta) vertex)
        (sixVertexLocalIncomingPattern
          (sixVertexTorusSwitchSecond mask omega eta) vertex) =
      sixVertexLocalDisagreementSides
        (sixVertexLocalIncomingPattern omega vertex)
        (sixVertexLocalIncomingPattern eta vertex) := by
    ext side
    simp only [mem_sixVertexLocalDisagreementSides]
    rw [sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees,
      sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees,
      sixVertexTorusEdgeDisagrees_pairSwitch_iff]
  rw [hsides]
  exact hdegree vertex


theorem sixVertexTorusMaskSelects_maskXor
    {T : EvenTorus} (first second : SixVertexArrows T)
    (edge : SixVertexTorusEdge T) :
    sixVertexTorusMaskSelects
        (sixVertexTorusMaskXor first second) edge =
      (sixVertexTorusMaskSelects first edge !=
        sixVertexTorusMaskSelects second edge) := by
  rcases edge with ⟨direction, base⟩
  fin_cases direction <;>
    simp [sixVertexTorusMaskSelects, sixVertexTorusMaskXor]


theorem sixVertexDisagreementComponentSetMask_symmDiff_selects
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (first second : Finset (SixVertexDisagreementComponent omega eta))
    (edge : SixVertexTorusEdge T) :
    sixVertexTorusMaskSelects
        (sixVertexDisagreementComponentSetMask omega eta
          (first ∆ second)) edge =
      (sixVertexTorusMaskSelects
          (sixVertexDisagreementComponentSetMask omega eta first) edge !=
        sixVertexTorusMaskSelects
          (sixVertexDisagreementComponentSetMask omega eta second) edge) := by
  classical
  apply Bool.eq_iff_iff.mpr
  rw [sixVertexDisagreementComponentSetMask_selects_iff,
    bne_iff_ne]
  constructor
  · rintro ⟨component, hcomponent, hedge⟩
    rw [Finset.mem_symmDiff] at hcomponent
    rcases hcomponent with ⟨hfirst, hsecond⟩ | ⟨hsecond, hfirst⟩
    · have hfirstSelect :=
        (sixVertexDisagreementComponentSetMask_selects_iff
          omega eta first edge).2 ⟨component, hfirst, hedge⟩
      have hsecondSelect : sixVertexTorusMaskSelects
          (sixVertexDisagreementComponentSetMask omega eta second)
          edge = false := by
        cases hs : sixVertexTorusMaskSelects
            (sixVertexDisagreementComponentSetMask omega eta second) edge
        · rfl
        · exfalso
          obtain ⟨other, hother, hotherEdge⟩ :=
            (sixVertexDisagreementComponentSetMask_selects_iff
              omega eta second edge).1 hs
          apply hsecond
          have : other = component := by
            apply Subtype.ext
            exact hotherEdge.symm.trans hedge
          simpa [this] using hother
      simp [hfirstSelect, hsecondSelect]
    · have hsecondSelect :=
        (sixVertexDisagreementComponentSetMask_selects_iff
          omega eta second edge).2 ⟨component, hsecond, hedge⟩
      have hfirstSelect : sixVertexTorusMaskSelects
          (sixVertexDisagreementComponentSetMask omega eta first)
          edge = false := by
        cases hs : sixVertexTorusMaskSelects
            (sixVertexDisagreementComponentSetMask omega eta first) edge
        · rfl
        · exfalso
          obtain ⟨other, hother, hotherEdge⟩ :=
            (sixVertexDisagreementComponentSetMask_selects_iff
              omega eta first edge).1 hs
          apply hfirst
          have : other = component := by
            apply Subtype.ext
            exact hotherEdge.symm.trans hedge
          simpa [this] using hother
      simp [hfirstSelect, hsecondSelect]
  · intro hne
    cases hfirstSelect : sixVertexTorusMaskSelects
        (sixVertexDisagreementComponentSetMask omega eta first) edge <;>
      cases hsecondSelect : sixVertexTorusMaskSelects
        (sixVertexDisagreementComponentSetMask omega eta second) edge
    · exact False.elim (hne (by rw [hfirstSelect, hsecondSelect]))
    · obtain ⟨component, hcomponent, hedge⟩ :=
        (sixVertexDisagreementComponentSetMask_selects_iff
          omega eta second edge).1 hsecondSelect
      refine ⟨component, (Finset.mem_symmDiff).2 (Or.inr
        ⟨hcomponent, ?_⟩), hedge⟩
      intro hmem
      have hfalse := (sixVertexDisagreementComponentSetMask_selects_iff
        omega eta first edge).2 ⟨component, hmem, hedge⟩
      rw [hfirstSelect] at hfalse
      exact Bool.noConfusion hfalse
    · obtain ⟨component, hcomponent, hedge⟩ :=
        (sixVertexDisagreementComponentSetMask_selects_iff
          omega eta first edge).1 hfirstSelect
      refine ⟨component, (Finset.mem_symmDiff).2 (Or.inl
        ⟨hcomponent, ?_⟩), hedge⟩
      intro hmem
      have hfalse := (sixVertexDisagreementComponentSetMask_selects_iff
        omega eta second edge).2 ⟨component, hmem, hedge⟩
      rw [hsecondSelect] at hfalse
      exact Bool.noConfusion hfalse
    · exact False.elim (hne (by rw [hfirstSelect, hsecondSelect]))


theorem sixVertexDisagreementComponentSetMask_symmDiff
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (first second : Finset (SixVertexDisagreementComponent omega eta)) :
    sixVertexDisagreementComponentSetMask omega eta (first ∆ second) =
      sixVertexTorusMaskXor
        (sixVertexDisagreementComponentSetMask omega eta first)
        (sixVertexDisagreementComponentSetMask omega eta second) := by
  apply SixVertexArrows.ext <;> funext base
  · simpa [sixVertexTorusMaskSelects, sixVertexTorusMaskXor] using
      sixVertexDisagreementComponentSetMask_symmDiff_selects
        omega eta first second (0, base)
  · simpa [sixVertexTorusMaskSelects, sixVertexTorusMaskXor] using
      sixVertexDisagreementComponentSetMask_symmDiff_selects
        omega eta first second (1, base)


theorem sixVertexTorusSwitchFirst_pairSwitch
    {T : EvenTorus} (first second omega eta : SixVertexArrows T) :
    sixVertexTorusSwitchFirst second
        (sixVertexTorusSwitchFirst first omega eta)
        (sixVertexTorusSwitchSecond first omega eta) =
      sixVertexTorusSwitchFirst (sixVertexTorusMaskXor first second)
        omega eta := by
  apply SixVertexArrows.ext <;> funext base <;>
    simp [sixVertexTorusSwitchFirst, sixVertexTorusSwitchSecond,
      sixVertexTorusMaskXor] <;>
    split <;> split <;> simp_all

theorem sixVertexTorusSwitchSecond_pairSwitch
    {T : EvenTorus} (first second omega eta : SixVertexArrows T) :
    sixVertexTorusSwitchSecond second
        (sixVertexTorusSwitchFirst first omega eta)
        (sixVertexTorusSwitchSecond first omega eta) =
      sixVertexTorusSwitchSecond (sixVertexTorusMaskXor first second)
        omega eta := by
  apply SixVertexArrows.ext <;> funext base <;>
    simp [sixVertexTorusSwitchFirst, sixVertexTorusSwitchSecond,
      sixVertexTorusMaskXor] <;>
    split <;> split <;> simp_all


theorem SixVertexFullDisagreementMask.selects_of_reachable
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hmask : SixVertexFullDisagreementMask omega eta mask)
    {seed edge : SixVertexTorusEdge T}
    (hseed : sixVertexTorusMaskSelects mask seed = true)
    (hreach : (sixVertexTorusDisagreementGraph omega eta).Reachable
      seed edge) :
    sixVertexTorusMaskSelects mask edge = true := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  induction hreach with
  | refl => exact hseed
  | tail first hadj ih =>
      obtain ⟨hne, _, hedge, vertex, firstSide, edgeSide,
        hfirst, hedgeEq⟩ := hadj
      rw [← hedgeEq, ← sixVertexTorusLocalSwitchMask_apply]
      apply hmask.2 vertex firstSide edgeSide
      · rw [sixVertexTorusLocalSwitchMask_apply, hfirst]
        exact ih
      · rw [sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees,
          hedgeEq]
        exact hedge


theorem sixVertexTorusIncidentEdge_injective
    (T : EvenTorus) (vertex : T.Vertex) :
    Function.Injective (sixVertexTorusIncidentEdge T vertex) := by
  intro first second heq
  fin_cases first <;> fin_cases second <;>
    simp_all [sixVertexTorusIncidentEdge, Prod.ext_iff,
      cyclicPred_ne_self T.one_lt_width vertex.1,
      cyclicPred_ne_self T.one_lt_height vertex.2]
  all_goals first
    | exact (cyclicPred_ne_self T.one_lt_width vertex.1) heq.symm
    | exact (cyclicPred_ne_self T.one_lt_height vertex.2) heq.symm


end
end StatMech.FrontierD
