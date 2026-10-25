/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Def.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part19
open StatMech.FrontierD


namespace ScratchLocalRetieC

theorem alignedBlackDartLayerSwap_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    alignedBlackDartLayerSwap homega heta hdegree
        (doubledAlignedBlackDart homega heta hdegree false x) =
      doubledAlignedBlackDart homega heta hdegree true x := by
  let activeFalse := doubledAlignedBlackDartEquiv
    homega heta hdegree false x
  have himage : (activeFalse : FKMedialBlackDart T) =
      (Equiv.refl {d : FKMedialBlackDart T //
        activeBlackDart (omega := omega) (eta := eta) d}) activeFalse := rfl
  change ((alignedActiveBlackDartLayerSwap homega heta hdegree).extendDomain
      (Equiv.refl {d : FKMedialBlackDart T //
        activeBlackDart (omega := omega) (eta := eta) d}))
      (activeFalse : FKMedialBlackDart T) = _
  rw [himage, Equiv.Perm.extendDomain_apply_image]
  change (alignedActiveBlackDartLayerSwap homega heta hdegree
      activeFalse).1 = _
  unfold alignedActiveBlackDartLayerSwap
  simp [activeFalse]
  rfl

theorem alignedBlackDartLayerSwap_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : FKMedialBlackDart T)
    (hinactive : Not (activeBlackDart (omega := omega) (eta := eta) d)) :
    alignedBlackDartLayerSwap homega heta hdegree d = d := by
  exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hinactive

theorem alignedBlackDartLayerSwap_power
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) (k : Nat)
    (hk : k < finiteFirstReturnTime
      (alignedBoundaryPerm homega heta hdegree false)
      (activeBlackDart (omega := omega) (eta := eta))
      (doubledAlignedBlackDartEquiv homega heta hdegree false x)) :
    alignedBlackDartLayerSwap homega heta hdegree
        ((alignedBoundaryPerm homega heta hdegree false ^ k)
          (doubledAlignedBlackDart homega heta hdegree false x)) =
      (alignedBoundaryPerm homega heta hdegree true ^ k)
        (doubledAlignedBlackDart homega heta hdegree true x) := by
  classical
  by_cases hkzero : k = 0
  · subst k
    simpa using alignedBlackDartLayerSwap_active
      homega heta hdegree x
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hkzero
    have htime := alignedFirstReturnTime_eq homega heta hdegree x
    have hrelated := finiteRelated_until_firstReturn
      (alignedBoundaryPerm homega heta hdegree false)
      (alignedBoundaryPerm homega heta hdegree true)
      (activeBlackDart (omega := omega) (eta := eta))
      (activeBlackDart (omega := omega) (eta := eta))
      (fun a b => a = b)
      (fun {a b} hab hnotA hnotB => by
        subst b
        apply blackBoundary_eq_of_pairing_eq_at
        apply alignedRoutingPairing_eq_layers_at_inactive
          homega heta hdegree a.1.1
        rcases hdegree a.1.1 with hzero | htwo
        · exact hzero
        · exact False.elim (hnotA htwo))
      (doubledAlignedBlackDartEquiv homega heta hdegree false x)
      (doubledAlignedBlackDartEquiv homega heta hdegree true x)
      (doubledAlignedBlackDart_first_step homega heta hdegree x)
      k hkpos (Nat.le_of_lt hk) (by omega)
    have hinactive : Not (activeBlackDart (omega := omega) (eta := eta)
        ((alignedBoundaryPerm homega heta hdegree false ^ k)
          (doubledAlignedBlackDart homega heta hdegree false x))) := by
      intro hactive
      exact (finiteFirstReturnTime_minimal
        (alignedBoundaryPerm homega heta hdegree false)
        (activeBlackDart (omega := omega) (eta := eta))
        (doubledAlignedBlackDartEquiv homega heta hdegree false x)
        k hk) ⟨hkpos, hactive⟩
    rw [alignedBlackDartLayerSwap_inactive
      homega heta hdegree _ hinactive]
    exact hrelated

theorem finiteFirstReturnSegment_aligned_eq_map_layerSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    finiteFirstReturnSegment
        (alignedBoundaryPerm homega heta hdegree true)
        (activeBlackDart (omega := omega) (eta := eta))
        (doubledAlignedBlackDartEquiv homega heta hdegree true x) =
      (finiteFirstReturnSegment
        (alignedBoundaryPerm homega heta hdegree false)
        (activeBlackDart (omega := omega) (eta := eta))
        (doubledAlignedBlackDartEquiv homega heta hdegree false x)).map
          (alignedBlackDartLayerSwap homega heta hdegree) := by
  classical
  apply List.ext_getElem
  · simp only [length_finiteFirstReturnSegment, List.length_map]
    exact (alignedFirstReturnTime_eq homega heta hdegree x).symm
  · intro k hkTrue hkMap
    simp only [finiteFirstReturnSegment, List.getElem_ofFn,
      List.getElem_map]
    exact (alignedBlackDartLayerSwap_power
      homega heta hdegree x k (by simpa using hkMap)).symm

theorem doubledAlignedBoundarySegments_eq_map_layerSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (states : List (DoubledAlignedState omega eta)) :
    doubledAlignedBoundarySegments homega heta hdegree true states =
      (doubledAlignedBoundarySegments
        homega heta hdegree false states).map
          (alignedBlackDartLayerSwap homega heta hdegree) := by
  classical
  induction states with
  | nil => simp [doubledAlignedBoundarySegments,
      finiteFirstReturnSegments]
  | cons x states ih =>
      simp only [doubledAlignedBoundarySegments,
        finiteFirstReturnSegments, List.map_cons, List.flatMap_cons,
        List.map_append]
      rw [finiteFirstReturnSegment_aligned_eq_map_layerSwap
        homega heta hdegree x]
      exact congrArg
        (List.append
          ((finiteFirstReturnSegment
            (alignedBoundaryPerm homega heta hdegree false)
            (activeBlackDart (omega := omega) (eta := eta))
            (doubledAlignedBlackDartEquiv
              homega heta hdegree false x)).map
                (alignedBlackDartLayerSwap homega heta hdegree))) ih


end ScratchLocalRetieC
