/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentBooleanOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentBooleanOrbit
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDisagreementComponentSetMask_selects_iff
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (selected : Finset (SixVertexDisagreementComponent omega eta))
    (edge : SixVertexTorusEdge T) :
    sixVertexTorusMaskSelects
        (sixVertexDisagreementComponentSetMask omega eta selected) edge = true
      ↔ ∃ component ∈ selected,
        (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk edge =
          component.1 := by
  classical
  rcases edge with ⟨direction, vertex⟩
  fin_cases direction <;>
    simp [sixVertexTorusMaskSelects,
      sixVertexDisagreementComponentSetMask]


theorem sixVertexDisagreementComponentSetMask_selects_only_disagreement
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (selected : Finset (SixVertexDisagreementComponent omega eta))
    (edge : SixVertexTorusEdge T)
    (hselected : sixVertexTorusMaskSelects
      (sixVertexDisagreementComponentSetMask omega eta selected) edge = true) :
    sixVertexTorusEdgeDisagrees omega eta edge := by
  obtain ⟨component, _, hedge⟩ :=
    (sixVertexDisagreementComponentSetMask_selects_iff
      omega eta selected edge).1 hselected
  obtain ⟨seed, hseed, hseedComponent⟩ := component.2
  apply sixVertexDisagreementGraph_reachable_disagrees hseed
  apply ConnectedComponent.exact
  exact hseedComponent.trans hedge.symm


theorem sixVertexDisagreementComponentSetMask_incident_closure
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (selected : Finset (SixVertexDisagreementComponent omega eta))
    (vertex : T.Vertex) (first second : Fin 4)
    (hfirst : sixVertexTorusMaskSelects
      (sixVertexDisagreementComponentSetMask omega eta selected)
        (sixVertexTorusIncidentEdge T vertex first) = true)
    (hsecond : sixVertexTorusEdgeDisagrees omega eta
      (sixVertexTorusIncidentEdge T vertex second)) :
    sixVertexTorusMaskSelects
      (sixVertexDisagreementComponentSetMask omega eta selected)
        (sixVertexTorusIncidentEdge T vertex second) = true := by
  let graph := sixVertexTorusDisagreementGraph omega eta
  obtain ⟨component, hcomponent, hfirstComponent⟩ :=
    (sixVertexDisagreementComponentSetMask_selects_iff omega eta selected
      (sixVertexTorusIncidentEdge T vertex first)).1 hfirst
  apply (sixVertexDisagreementComponentSetMask_selects_iff omega eta selected
    (sixVertexTorusIncidentEdge T vertex second)).2
  refine ⟨component, hcomponent, ?_⟩
  by_cases hedges : sixVertexTorusIncidentEdge T vertex first =
      sixVertexTorusIncidentEdge T vertex second
  · simpa [hedges] using hfirstComponent
  · have hfirstDisagrees :=
      sixVertexDisagreementComponentSetMask_selects_only_disagreement
        omega eta selected _ hfirst
    have hadj : graph.Adj
        (sixVertexTorusIncidentEdge T vertex first)
        (sixVertexTorusIncidentEdge T vertex second) :=
      ⟨hedges, hfirstDisagrees, hsecond,
        vertex, first, second, rfl, rfl⟩
    exact (ConnectedComponent.sound hadj.reachable).symm.trans
      hfirstComponent


theorem sixVertexDisagreementComponentSetMask_full
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (selected : Finset (SixVertexDisagreementComponent omega eta)) :
    SixVertexFullDisagreementMask omega eta
      (sixVertexDisagreementComponentSetMask omega eta selected) := by
  constructor
  · intro vertex side hside
    rw [sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees]
    apply sixVertexDisagreementComponentSetMask_selects_only_disagreement
      omega eta selected
    rwa [sixVertexTorusLocalSwitchMask_apply] at hside
  · intro vertex first second hfirst hsecond
    rw [sixVertexTorusLocalSwitchMask_apply] at hfirst ⊢
    apply sixVertexDisagreementComponentSetMask_incident_closure
      omega eta selected vertex first second hfirst
    exact (sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
      omega eta vertex second).1 hsecond


theorem sixVertexDisagreementComponent_mem_iff_mask_selects
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (selected : Finset (SixVertexDisagreementComponent omega eta))
    (component : SixVertexDisagreementComponent omega eta)
    (edge : SixVertexTorusEdge T)
    (hcomponent :
      (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk edge =
        component.1) :
    component ∈ selected ↔
      sixVertexTorusMaskSelects
        (sixVertexDisagreementComponentSetMask omega eta selected) edge = true := by
  constructor
  · intro hmem
    apply (sixVertexDisagreementComponentSetMask_selects_iff
      omega eta selected edge).2
    exact ⟨component, hmem, hcomponent⟩
  · intro hselected
    obtain ⟨other, hother, hotherComponent⟩ :=
      (sixVertexDisagreementComponentSetMask_selects_iff
        omega eta selected edge).1 hselected
    have : other = component := by
      apply Subtype.ext
      exact hotherComponent.symm.trans hcomponent
    simpa [this] using hother


theorem sixVertexDisagreementComponentSetMask_injective
    {T : EvenTorus} (omega eta : SixVertexArrows T) :
    Function.Injective
      (sixVertexDisagreementComponentSetMask omega eta) := by
  classical
  intro first second hmasks
  ext component
  obtain ⟨edge, _, hcomponent⟩ := component.2
  rw [sixVertexDisagreementComponent_mem_iff_mask_selects omega eta first
      component edge hcomponent,
    sixVertexDisagreementComponent_mem_iff_mask_selects omega eta second
      component edge hcomponent,
    hmasks]


end
end StatMech.FrontierD
