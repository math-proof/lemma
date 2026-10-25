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
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoComponentStrand
open Finset SimpleGraph
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoOrientedComponentEdge_successor_adj
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : SixVertexOrientedDisagreementDart omega eta) :
    (sixVertexTorusDisagreementGraph omega eta).Adj
      (sixVertexDegreeTwoOrientedComponentEdge hdegree dart)
      (sixVertexDegreeTwoOrientedComponentEdge hdegree
        (sixVertexOrientedDegreeTwoStrandSuccessor
          homega heta hdegree dart)) := by
  let outgoing := sixVertexDegreeTwoLocalMate hdegree dart.1
  let successor := sixVertexDisagreementBondMate outgoing
  have hsuccessor :
      (sixVertexOrientedDegreeTwoStrandSuccessor
        homega heta hdegree dart).1 = successor := rfl
  have hfirst : sixVertexDegreeTwoOrientedComponentEdge hdegree dart =
      sixVertexTorusDartEdge T outgoing.1 := rfl
  have hsecond : sixVertexDegreeTwoOrientedComponentEdge hdegree
        (sixVertexOrientedDegreeTwoStrandSuccessor
          homega heta hdegree dart) =
      sixVertexTorusDartEdge T
        (sixVertexDegreeTwoLocalMate hdegree successor).1 := by
    rfl
  have hfirstIncident : sixVertexTorusDartEdge T outgoing.1 =
      sixVertexTorusIncidentEdge T successor.1.1 successor.1.2 := by
    change sixVertexTorusDartEdge T outgoing.1 =
      sixVertexTorusDartEdge T successor.1
    exact (sixVertexTorusDartEdge_bondMate T outgoing.1).symm
  rw [hfirst, hsecond]
  refine ⟨?_, outgoing.2,
    (sixVertexDegreeTwoLocalMate hdegree successor).2,
    successor.1.1, successor.1.2,
    (sixVertexDegreeTwoLocalMate hdegree successor).1.2, ?_, ?_⟩
  · intro hedge
    have hsides := (sixVertexTorusIncidentEdge_injective T successor.1.1)
      (hfirstIncident.symm.trans hedge)
    exact (sixVertexDegreeTwoLocalMate_side_ne hdegree successor)
      hsides.symm
  · exact hfirstIncident.symm
  · rfl


theorem sixVertexDegreeTwoOrientedComponentEdge_eq_of_sameCycle
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (first second : SixVertexOrientedDisagreementDart omega eta)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle first second) :
    (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk
        (sixVertexDegreeTwoOrientedComponentEdge hdegree first) =
      (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk
        (sixVertexDegreeTwoOrientedComponentEdge hdegree second) := by
  let successor := sixVertexOrientedDegreeTwoStrandSuccessor
    homega heta hdegree
  obtain ⟨power, hpower⟩ := hsame.exists_nat_pow_eq
  have hpow : forall n : Nat,
      (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk
          (sixVertexDegreeTwoOrientedComponentEdge hdegree first) =
        (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk
          (sixVertexDegreeTwoOrientedComponentEdge hdegree
            ((successor ^ n) first)) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact ih.trans (ConnectedComponent.sound
          (sixVertexDegreeTwoOrientedComponentEdge_successor_adj
            homega heta hdegree ((successor ^ n) first)).reachable)
  simpa [successor, hpower] using hpow power


theorem sixVertexDegreeTwoStrand_mask_component
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta)
    (edge : SixVertexTorusEdge T)
    (hselected : sixVertexTorusMaskSelects
      (sixVertexDegreeTwoStrandDirectedSimpleCycle
        homega heta hdegree seed).mask edge = true) :
    (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk edge =
      (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk
        (sixVertexDegreeTwoOrientedComponentEdge hdegree seed) := by
  rcases edge with ⟨direction, base⟩
  fin_cases direction
  · obtain ⟨index, hindex⟩ :=
      ((sixVertexDegreeTwoStrandDirectedSimpleCycle
        homega heta hdegree seed).mask_horizontal base).1 (by
          simpa [sixVertexTorusMaskSelects] using hselected)
    have hedge : sixVertexDegreeTwoOrientedComponentEdge hdegree
          (sixVertexDegreeTwoStrandCycleEnumeration
            homega heta hdegree seed index) = (0, base) := by
      exact sixVertexDirectedTorusEdgeOfArrow_physical_injective omega
        (by simpa [sixVertexDegreeTwoStrandDirectedSimpleCycle,
            sixVertexDegreeTwoDirectedSimpleCycleOfEnumeration,
            sixVertexDegreeTwoOrientedStrandEdge,
            SixVertexDirectedTorusEdge.physical] using hindex)
    change (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk
        (0, base) = _
    rw [← hedge]
    exact (sixVertexDegreeTwoOrientedComponentEdge_eq_of_sameCycle
      homega heta hdegree seed _
      (sixVertexDegreeTwoStrandCycleEnumeration_sameCycle
        homega heta hdegree seed index)).symm
  · obtain ⟨index, hindex⟩ :=
      ((sixVertexDegreeTwoStrandDirectedSimpleCycle
        homega heta hdegree seed).mask_vertical base).1 (by
          simpa [sixVertexTorusMaskSelects] using hselected)
    have hedge : sixVertexDegreeTwoOrientedComponentEdge hdegree
          (sixVertexDegreeTwoStrandCycleEnumeration
            homega heta hdegree seed index) = (1, base) := by
      exact sixVertexDirectedTorusEdgeOfArrow_physical_injective omega
        (by simpa [sixVertexDegreeTwoStrandDirectedSimpleCycle,
            sixVertexDegreeTwoDirectedSimpleCycleOfEnumeration,
            sixVertexDegreeTwoOrientedStrandEdge,
            SixVertexDirectedTorusEdge.physical] using hindex)
    change (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk
        (1, base) = _
    rw [← hedge]
    exact (sixVertexDegreeTwoOrientedComponentEdge_eq_of_sameCycle
      homega heta hdegree seed _
      (sixVertexDegreeTwoStrandCycleEnumeration_sameCycle
        homega heta hdegree seed index)).symm


theorem sixVertexDegreeTwoStrand_mask_seedEdge
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    sixVertexTorusMaskSelects
      (sixVertexDegreeTwoStrandDirectedSimpleCycle
        homega heta hdegree seed).mask
      (sixVertexDegreeTwoOrientedComponentEdge hdegree seed) = true := by
  let zero : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed)) :=
    ⟨0, orderOf_pos (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed)⟩
  rcases hedge : sixVertexDegreeTwoOrientedComponentEdge hdegree seed with
    ⟨direction, base⟩
  fin_cases direction
  · apply ((sixVertexDegreeTwoStrandDirectedSimpleCycle
      homega heta hdegree seed).mask_horizontal base).2
    refine ⟨zero, ?_⟩
    change (sixVertexDirectedTorusEdgeOfArrow omega
      (sixVertexDegreeTwoOrientedComponentEdge hdegree
        (sixVertexDegreeTwoStrandCycleEnumeration
          homega heta hdegree seed zero))).physical = (false, base)
    rw [show sixVertexDegreeTwoStrandCycleEnumeration
      homega heta hdegree seed zero = seed by rfl, hedge]
    simp [sixVertexDirectedTorusEdgeOfArrow,
      SixVertexDirectedTorusEdge.physical]
  · apply ((sixVertexDegreeTwoStrandDirectedSimpleCycle
      homega heta hdegree seed).mask_vertical base).2
    refine ⟨zero, ?_⟩
    change (sixVertexDirectedTorusEdgeOfArrow omega
      (sixVertexDegreeTwoOrientedComponentEdge hdegree
        (sixVertexDegreeTwoStrandCycleEnumeration
          homega heta hdegree seed zero))).physical = (true, base)
    rw [show sixVertexDegreeTwoStrandCycleEnumeration
      homega heta hdegree seed zero = seed by rfl, hedge]
    simp [sixVertexDirectedTorusEdgeOfArrow,
      SixVertexDirectedTorusEdge.physical]


theorem sixVertexDegreeTwoStrand_mask_full
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    SixVertexFullDisagreementMask omega eta
      (sixVertexDegreeTwoStrandDirectedSimpleCycle
        homega heta hdegree seed).mask := by
  have hbalanced : SixVertexBalancedFlipMask omega
      (sixVertexDegreeTwoStrandDirectedSimpleCycle
        homega heta hdegree seed).mask :=
    sixVertexBalancedFlipMask_of_ice_flip homega
      (sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_ice
        homega heta hdegree seed)
  exact hbalanced.fullDisagreementMask_of_degreeTwo hdegree
    (sixVertexDegreeTwoStrandDirectedSimpleCycle_mask_disagrees
      homega heta hdegree seed)


theorem sixVertexDegreeTwoStrand_mask_eq_component
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component : SixVertexDisagreementComponent omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta)
    (hseed : (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk
        (sixVertexDegreeTwoOrientedComponentEdge hdegree seed) = component.1) :
    (sixVertexDegreeTwoStrandDirectedSimpleCycle
        homega heta hdegree seed).mask =
      sixVertexDisagreementComponentSetMask omega eta {component} := by
  let strandMask := (sixVertexDegreeTwoStrandDirectedSimpleCycle
    homega heta hdegree seed).mask
  let componentMask :=
    sixVertexDisagreementComponentSetMask omega eta {component}
  have hstrandFull := sixVertexDegreeTwoStrand_mask_full
    homega heta hdegree seed
  have hcomponentFull := sixVertexDisagreementComponentSetMask_full
    omega eta {component}
  have hstrandSeed := sixVertexDegreeTwoStrand_mask_seedEdge
    homega heta hdegree seed
  apply SixVertexArrows.ext <;> funext base
  · apply Bool.eq_iff_iff.mpr
    constructor
    · intro hstrand
      apply (sixVertexDisagreementComponentSetMask_selects_iff
        omega eta {component} (0, base)).2
      refine ⟨component, by simp, ?_⟩
      exact (sixVertexDegreeTwoStrand_mask_component
        homega heta hdegree seed (0, base) (by
          simpa [strandMask, sixVertexTorusMaskSelects] using hstrand)).trans
        hseed
    · intro hcomponent
      have hcomponentEq :=
        (sixVertexDisagreementComponentSetMask_selects_iff
          omega eta {component} (0, base)).1 (by
            simpa [componentMask, sixVertexTorusMaskSelects] using hcomponent)
      obtain ⟨other, hother, hedge⟩ := hcomponentEq
      have : other = component := by simpa using hother
      subst other
      have hselected := hstrandFull.selects_of_reachable hstrandSeed
        (ConnectedComponent.exact (hseed.trans hedge.symm))
      simpa [sixVertexTorusMaskSelects] using hselected
  · apply Bool.eq_iff_iff.mpr
    constructor
    · intro hstrand
      apply (sixVertexDisagreementComponentSetMask_selects_iff
        omega eta {component} (1, base)).2
      refine ⟨component, by simp, ?_⟩
      exact (sixVertexDegreeTwoStrand_mask_component
        homega heta hdegree seed (1, base) (by
          simpa [strandMask, sixVertexTorusMaskSelects] using hstrand)).trans
        hseed
    · intro hcomponent
      have hcomponentEq :=
        (sixVertexDisagreementComponentSetMask_selects_iff
          omega eta {component} (1, base)).1 (by
            simpa [componentMask, sixVertexTorusMaskSelects] using hcomponent)
      obtain ⟨other, hother, hedge⟩ := hcomponentEq
      have : other = component := by simpa using hother
      subst other
      have hselected := hstrandFull.selects_of_reachable hstrandSeed
        (ConnectedComponent.exact (hseed.trans hedge.symm))
      simpa [sixVertexTorusMaskSelects] using hselected


theorem sixVertexDegreeTwoStrand_mask_eq_reference_component
    {T : EvenTorus} {omega eta referenceFirst referenceSecond :
      SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (hgraph : sixVertexTorusDisagreementGraph omega eta =
      sixVertexTorusDisagreementGraph referenceFirst referenceSecond)
    (component : SixVertexDisagreementComponent
      referenceFirst referenceSecond)
    (seed : SixVertexOrientedDisagreementDart omega eta)
    (hseed : (sixVertexTorusDisagreementGraph
        referenceFirst referenceSecond).connectedComponentMk
          (sixVertexDegreeTwoOrientedComponentEdge hdegree seed) =
      component.1) :
    (sixVertexDegreeTwoStrandDirectedSimpleCycle
        homega heta hdegree seed).mask =
      sixVertexDisagreementComponentSetMask
        referenceFirst referenceSecond {component} := by
  let strandMask := (sixVertexDegreeTwoStrandDirectedSimpleCycle
    homega heta hdegree seed).mask
  have hstrandFull := sixVertexDegreeTwoStrand_mask_full
    homega heta hdegree seed
  have hstrandSeed := sixVertexDegreeTwoStrand_mask_seedEdge
    homega heta hdegree seed
  apply SixVertexArrows.ext <;> funext base
  · apply Bool.eq_iff_iff.mpr
    constructor
    · intro hstrand
      apply (sixVertexDisagreementComponentSetMask_selects_iff
        referenceFirst referenceSecond {component} (0, base)).2
      refine ⟨component, by simp, ?_⟩
      have hcomponent := sixVertexDegreeTwoStrand_mask_component
        homega heta hdegree seed (0, base) (by
          simpa [strandMask, sixVertexTorusMaskSelects] using hstrand)
      rw [hgraph] at hcomponent
      exact hcomponent.trans hseed
    · intro hcomponent
      obtain ⟨other, hother, hedge⟩ :=
        (sixVertexDisagreementComponentSetMask_selects_iff
          referenceFirst referenceSecond {component} (0, base)).1 (by
            simpa [sixVertexTorusMaskSelects] using hcomponent)
      have : other = component := by simpa using hother
      subst other
      have hreach : (sixVertexTorusDisagreementGraph omega eta).Reachable
          (sixVertexDegreeTwoOrientedComponentEdge hdegree seed)
          (0, base) := by
        rw [hgraph]
        exact ConnectedComponent.exact (hseed.trans hedge.symm)
      have hselected := hstrandFull.selects_of_reachable
        hstrandSeed hreach
      simpa [sixVertexTorusMaskSelects] using hselected
  · apply Bool.eq_iff_iff.mpr
    constructor
    · intro hstrand
      apply (sixVertexDisagreementComponentSetMask_selects_iff
        referenceFirst referenceSecond {component} (1, base)).2
      refine ⟨component, by simp, ?_⟩
      have hcomponent := sixVertexDegreeTwoStrand_mask_component
        homega heta hdegree seed (1, base) (by
          simpa [strandMask, sixVertexTorusMaskSelects] using hstrand)
      rw [hgraph] at hcomponent
      exact hcomponent.trans hseed
    · intro hcomponent
      obtain ⟨other, hother, hedge⟩ :=
        (sixVertexDisagreementComponentSetMask_selects_iff
          referenceFirst referenceSecond {component} (1, base)).1 (by
            simpa [sixVertexTorusMaskSelects] using hcomponent)
      have : other = component := by simpa using hother
      subst other
      have hreach : (sixVertexTorusDisagreementGraph omega eta).Reachable
          (sixVertexDegreeTwoOrientedComponentEdge hdegree seed)
          (1, base) := by
        rw [hgraph]
        exact ConnectedComponent.exact (hseed.trans hedge.symm)
      have hselected := hstrandFull.selects_of_reachable
        hstrandSeed hreach
      simpa [sixVertexTorusMaskSelects] using hselected

end
end StatMech.FrontierD
