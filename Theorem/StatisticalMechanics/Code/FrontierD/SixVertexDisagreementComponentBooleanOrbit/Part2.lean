/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentBooleanOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentBooleanOrbit.Part2
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDisagreementComponentSetMask_seamTransfer
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (selected : Finset (SixVertexDisagreementComponent omega eta)) :
    sixVertexTorusMaskSeamTransfer
        (sixVertexDisagreementComponentSetMask omega eta selected) omega eta =
      ∑ component ∈ selected,
        sixVertexDisagreementComponentCharge omega eta component := by
  classical
  unfold sixVertexTorusMaskSeamTransfer
    sixVertexDisagreementComponentCharge
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro column _
  let edge : SixVertexTorusEdge T :=
    (1, (column, svFinLast T.height_pos))
  let graph := sixVertexTorusDisagreementGraph omega eta
  let difference : Int :=
    (eta.vertical (column, svFinLast T.height_pos)).toNat -
      (omega.vertical (column, svFinLast T.height_pos)).toNat
  by_cases hexists : ∃ component ∈ selected,
      graph.connectedComponentMk edge = component.1
  · obtain ⟨component, hcomponent, hedge⟩ := hexists
    have hsum : (∑ other ∈ selected,
        if graph.connectedComponentMk edge = other.1 then difference
        else 0) = difference := by
      calc
        (∑ other ∈ selected,
            if graph.connectedComponentMk edge = other.1 then difference
            else 0) =
            (if graph.connectedComponentMk edge = component.1 then
              difference else 0) := by
          apply Finset.sum_eq_single component
          · intro other hother hne
            have hcomponentNe :
                graph.connectedComponentMk edge ≠ other.1 := by
              intro heq
              apply hne
              apply Subtype.ext
              exact heq.symm.trans hedge
            simp [hcomponentNe]
          · intro hnot
            exact False.elim (hnot hcomponent)
        _ = difference := by simp [hedge]
    have hmask :
        (sixVertexDisagreementComponentSetMask omega eta selected).vertical
          (column, svFinLast T.height_pos) = true := by
      simpa [edge, graph, sixVertexTorusMaskSelects] using
        (sixVertexDisagreementComponentSetMask_selects_iff
          omega eta selected edge).2 ⟨component, hcomponent, hedge⟩
    simpa [difference, hmask] using hsum.symm
  · have hsum : (∑ other ∈ selected,
        if graph.connectedComponentMk edge = other.1 then difference
        else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro component hcomponent
      have hne : graph.connectedComponentMk edge ≠ component.1 := by
        intro heq
        exact hexists ⟨component, hcomponent, heq⟩
      simp [hne]
    have hmask :
        (sixVertexDisagreementComponentSetMask omega eta selected).vertical
          (column, svFinLast T.height_pos) = false := by
      cases hm :
          (sixVertexDisagreementComponentSetMask omega eta selected).vertical
            (column, svFinLast T.height_pos)
      · rfl
      · exfalso
        apply hexists
        exact (sixVertexDisagreementComponentSetMask_selects_iff
          omega eta selected edge).1 (by
            simpa [edge, sixVertexTorusMaskSelects] using hm)
    simpa [difference, hmask] using hsum.symm


theorem sixVertexDisagreementComponentSetMask_seamTransfer_of_unit
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (hunit : forall component : SixVertexDisagreementComponent omega eta,
      sixVertexDisagreementComponentCharge omega eta component = 1)
    (selected : Finset (SixVertexDisagreementComponent omega eta)) :
    sixVertexTorusMaskSeamTransfer
        (sixVertexDisagreementComponentSetMask omega eta selected) omega eta =
      selected.card := by
  rw [sixVertexDisagreementComponentSetMask_seamTransfer]
  simp_rw [hunit]
  simp


theorem SixVertexFullDisagreementMask.of_pairSwitch
    {T : EvenTorus} {omega eta firstMask secondMask : SixVertexArrows T}
    (hfirst : SixVertexFullDisagreementMask omega eta firstMask) :
    SixVertexFullDisagreementMask
      (sixVertexTorusSwitchFirst secondMask omega eta)
      (sixVertexTorusSwitchSecond secondMask omega eta) firstMask := by
  constructor
  · intro vertex side hselected
    rw [sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees,
      sixVertexTorusEdgeDisagrees_pairSwitch_iff]
    exact (sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
      omega eta vertex side).1 (hfirst.1 vertex side hselected)
  · intro vertex first second hselected hsecond
    apply hfirst.2 vertex first second hselected
    rw [sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees] at hsecond ⊢
    exact (sixVertexTorusEdgeDisagrees_pairSwitch_iff
      secondMask omega eta _).1 hsecond


theorem SixVertexFullDisagreementMask.switchFirst_ice
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hmask : SixVertexFullDisagreementMask omega eta mask)
    (homega : omega.IceRule) (heta : eta.IceRule) :
    (sixVertexTorusSwitchFirst mask omega eta).IceRule := by
  intro vertex
  rw [← sixVertexLocalIncomingPattern_count]
  rcases hmask.local_eq_or_swap vertex with hsame | hswap
  · have hfirst := congrArg Prod.fst hsame
    change sixVertexLocalIncomingPattern
      (sixVertexTorusSwitchFirst mask omega eta) vertex =
        sixVertexLocalIncomingPattern omega vertex at hfirst
    rw [hfirst, sixVertexLocalIncomingPattern_count]
    exact homega vertex
  · have hfirst := congrArg Prod.fst hswap
    change sixVertexLocalIncomingPattern
      (sixVertexTorusSwitchFirst mask omega eta) vertex =
        sixVertexLocalIncomingPattern eta vertex at hfirst
    rw [hfirst, sixVertexLocalIncomingPattern_count]
    exact heta vertex


theorem SixVertexFullDisagreementMask.switchSecond_ice
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hmask : SixVertexFullDisagreementMask omega eta mask)
    (homega : omega.IceRule) (heta : eta.IceRule) :
    (sixVertexTorusSwitchSecond mask omega eta).IceRule := by
  intro vertex
  rw [← sixVertexLocalIncomingPattern_count]
  rcases hmask.local_eq_or_swap vertex with hsame | hswap
  · have hsecond := congrArg Prod.snd hsame
    change sixVertexLocalIncomingPattern
      (sixVertexTorusSwitchSecond mask omega eta) vertex =
        sixVertexLocalIncomingPattern eta vertex at hsecond
    rw [hsecond, sixVertexLocalIncomingPattern_count]
    exact heta vertex
  · have hsecond := congrArg Prod.snd hswap
    change sixVertexLocalIncomingPattern
      (sixVertexTorusSwitchSecond mask omega eta) vertex =
        sixVertexLocalIncomingPattern omega vertex at hsecond
    rw [hsecond, sixVertexLocalIncomingPattern_count]
    exact homega vertex

end
end StatMech.FrontierD
