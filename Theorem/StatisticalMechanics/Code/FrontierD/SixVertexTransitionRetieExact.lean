/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotRoute.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialUnitWindingSplitHall
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMedialCutAlignment.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLayeredCutBalance
open Equiv


namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}

theorem fkMedialTogglePairingAt_comm
    (pairing : FKMedialLoopPairing T) (first second : T.Vertex) :
    fkMedialTogglePairingAt
        (fkMedialTogglePairingAt pairing first) second =
      fkMedialTogglePairingAt
        (fkMedialTogglePairingAt pairing second) first := by
  by_cases hvertices : first = second
  · subst second
    rfl
  funext v
  by_cases hvFirst : v = first <;>
    by_cases hvSecond : v = second <;>
    simp [fkMedialTogglePairingAt, hvFirst, hvSecond,
      hvertices, Ne.symm hvertices]

@[simp] theorem sixVertexRetieAtTransitionVertices_self
    (pairing : FKMedialLoopPairing T) (first second : T.Vertex) :
    sixVertexRetieAtTransitionVertices
        (sixVertexRetieAtTransitionVertices pairing first second)
        first second = pairing := by
  by_cases hvertices : first = second
  · subst second
    simp [sixVertexRetieAtTransitionVertices]
  · rw [sixVertexRetieAtTransitionVertices,
      if_neg hvertices, sixVertexRetieAtTransitionVertices,
      if_neg hvertices]
    rw [fkMedialTogglePairingAt_comm _ second first,
      fkMedialTogglePairingAt_toggle,
      fkMedialTogglePairingAt_toggle]

theorem sixVertexRetieAtTransitionVertices_of_eq
    (pairing : FKMedialLoopPairing T) {first second : T.Vertex}
    (hvertices : first = second) :
    sixVertexRetieAtTransitionVertices pairing first second =
      fkMedialTogglePairingAt pairing first := by
  simp [sixVertexRetieAtTransitionVertices, hvertices]

theorem sixVertexRetieAtTransitionVertices_of_ne
    (pairing : FKMedialLoopPairing T) {first second : T.Vertex}
    (hvertices : first ≠ second) :
    sixVertexRetieAtTransitionVertices pairing first second =
      fkMedialTogglePairingAt
        (fkMedialTogglePairingAt pairing first) second := by
  simp [sixVertexRetieAtTransitionVertices, hvertices]

theorem fkMedialBlackBoundaryPerm_retie_of_eq
    (pairing : FKMedialLoopPairing T) {first second : T.Vertex}
    (hvertices : first = second) :
    fkMedialBlackBoundaryPerm
        (sixVertexRetieAtTransitionVertices pairing first second) =
      fkMedialBlackBoundaryPerm pairing *
        fkMedialBlackDartSwap first := by
  rw [sixVertexRetieAtTransitionVertices_of_eq pairing hvertices,
    fkMedialBlackBoundaryPerm_toggle]

theorem fkMedialBlackBoundaryPerm_retie_of_ne
    (pairing : FKMedialLoopPairing T) {first second : T.Vertex}
    (hvertices : first ≠ second) :
    fkMedialBlackBoundaryPerm
        (sixVertexRetieAtTransitionVertices pairing first second) =
      (fkMedialBlackBoundaryPerm pairing *
          fkMedialBlackDartSwap first) *
        fkMedialBlackDartSwap second := by
  rw [sixVertexRetieAtTransitionVertices_of_ne pairing hvertices,
    fkMedialBlackBoundaryPerm_toggle,
    fkMedialBlackBoundaryPerm_toggle]


theorem fkColoredStrandSlotBoundaryPerm_retie_of_eq
    (pairing : FKMedialLoopPairing T) {first second : T.Vertex}
    (hvertices : first = second) :
    fkColoredStrandSlotBoundaryPerm
        (sixVertexRetieAtTransitionVertices pairing first second) =
      if fkMedialVertexParity first = true then
        (fkColoredStrandSlotBoundaryPerm pairing).trans
          (fkColoredVertexStrandSlotSwap first)
      else
        (fkColoredVertexStrandSlotSwap first).trans
          (fkColoredStrandSlotBoundaryPerm pairing) := by
  rw [sixVertexRetieAtTransitionVertices_of_eq pairing hvertices,
    fkColoredStrandSlotBoundaryPerm_toggle]


theorem fkColoredStrandSlotBoundaryPerm_retie_of_ne
    (pairing : FKMedialLoopPairing T) {first second : T.Vertex}
    (hvertices : first != second) :
    fkColoredStrandSlotBoundaryPerm
        (sixVertexRetieAtTransitionVertices pairing first second) =
      if fkMedialVertexParity second = true then
        (if fkMedialVertexParity first = true then
            (fkColoredStrandSlotBoundaryPerm pairing).trans
              (fkColoredVertexStrandSlotSwap first)
          else
            (fkColoredVertexStrandSlotSwap first).trans
              (fkColoredStrandSlotBoundaryPerm pairing)).trans
          (fkColoredVertexStrandSlotSwap second)
      else
        (fkColoredVertexStrandSlotSwap second).trans
          (if fkMedialVertexParity first = true then
            (fkColoredStrandSlotBoundaryPerm pairing).trans
              (fkColoredVertexStrandSlotSwap first)
          else
            (fkColoredVertexStrandSlotSwap first).trans
              (fkColoredStrandSlotBoundaryPerm pairing)) := by
  have hne : first ≠ second := by
    simpa only [bne_iff_ne] using hvertices
  rw [sixVertexRetieAtTransitionVertices_of_ne pairing hne,
    fkColoredStrandSlotBoundaryPerm_toggle,
    fkColoredStrandSlotBoundaryPerm_toggle]


theorem doubledAlignedFirstReturnPerm_sameCycle_falseBoundary
    {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    {x y : DoubledAlignedState omega eta}
    (hcycle : (doubledAlignedFirstReturnPerm homega heta hdegree).SameCycle
      x y) :
    (alignedBoundaryPerm homega heta hdegree false).SameCycle
      (doubledAlignedBlackDart homega heta hdegree false x)
      (doubledAlignedBlackDart homega heta hdegree false y) := by
  classical
  let e := doubledAlignedBlackDartEquiv homega heta hdegree false
  let rho := finiteFirstReturnPerm
    (alignedBoundaryPerm homega heta hdegree false)
    (activeBlackDart (omega := omega) (eta := eta))
  have hdef : doubledAlignedFirstReturnPerm homega heta hdegree =
      e.symm.permCongr rho := rfl
  rw [hdef] at hcycle
  have hrho : rho.SameCycle (e x) (e y) := by
    rcases hcycle with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply e.symm.injective
    simp only [Equiv.symm_apply_apply]
    change (e.symm.permCongr (rho ^ n)) x = y
    have hmap := map_zpow e.symm.permCongrHom rho n
    change e.symm.permCongr (rho ^ n) =
      (e.symm.permCongr rho) ^ n at hmap
    rw [hmap]
    exact hn
  exact finiteFirstReturnPerm_sameCycle_ambient
    (alignedBoundaryPerm homega heta hdegree false)
    (activeBlackDart (omega := omega) (eta := eta)) (e x) (e y) hrho


end
end StatMech.FrontierD
