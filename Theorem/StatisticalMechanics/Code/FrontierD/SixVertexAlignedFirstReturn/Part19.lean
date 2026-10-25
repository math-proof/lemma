/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
import Def.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part21
open StatMech.FrontierD


namespace StatMech.FrontierD

theorem doubledAlignedBoundarySegments_nodup
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (states : List (DoubledAlignedState omega eta))
    (hstates : states.Nodup) :
    (doubledAlignedBoundarySegments
      homega heta hdegree layer states).Nodup := by
  classical
  apply finiteFirstReturnSegments_nodup
  exact hstates.map
    (doubledAlignedBlackDartEquiv homega heta hdegree layer).injective

theorem mem_doubledAlignedBoundarySegments_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (states : List (DoubledAlignedState omega eta))
    (d : FKMedialBlackDart T) :
    d ∈ doubledAlignedBoundarySegments homega heta hdegree layer states ↔
      ∃ x ∈ states, ∃ k : Nat,
        k < finiteFirstReturnTime
          (alignedBoundaryPerm homega heta hdegree layer)
          (activeBlackDart (omega := omega) (eta := eta))
          (doubledAlignedBlackDartEquiv homega heta hdegree layer x) ∧
        (alignedBoundaryPerm homega heta hdegree layer ^ k)
          (doubledAlignedBlackDart homega heta hdegree layer x) = d := by
  classical
  simp only [doubledAlignedBoundarySegments, finiteFirstReturnSegments,
    List.mem_flatMap, List.mem_map, finiteFirstReturnSegment,
    List.mem_ofFn]
  constructor
  · rintro ⟨active, ⟨x, hx, rfl⟩, ⟨k, hk⟩⟩
    exact ⟨x, hx, k.val, k.isLt, hk⟩
  · rintro ⟨x, hx, k, hk, hd⟩
    exact ⟨doubledAlignedBlackDartEquiv
      homega heta hdegree layer x, ⟨x, hx, rfl⟩,
      ⟨⟨k, hk⟩, hd⟩⟩

theorem mem_doubledAlignedBoundarySegments_step_iff_of_inactive_arrival
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (states : List (DoubledAlignedState omega eta))
    (dart : FKMedialBlackDart T)
    (hinactive : Not (activeBlackDart (omega := omega) (eta := eta)
      (alignedBoundaryPerm homega heta hdegree layer dart))) :
    alignedBoundaryPerm homega heta hdegree layer dart ∈
        doubledAlignedBoundarySegments homega heta hdegree layer states ↔
      dart ∈ doubledAlignedBoundarySegments
        homega heta hdegree layer states := by
  exact mem_finiteFirstReturnSegments_step_iff_of_not_selected
    (alignedBoundaryPerm homega heta hdegree layer)
    (activeBlackDart (omega := omega) (eta := eta))
    (states.map (doubledAlignedBlackDartEquiv
      homega heta hdegree layer)) dart hinactive

theorem doubledAlignedBlackDart_mem_boundarySegments_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (states : List (DoubledAlignedState omega eta))
    (y : DoubledAlignedState omega eta) :
    doubledAlignedBlackDart homega heta hdegree layer y ∈
        doubledAlignedBoundarySegments
          homega heta hdegree layer states ↔
      y ∈ states := by
  classical
  rw [mem_doubledAlignedBoundarySegments_iff]
  constructor
  · rintro ⟨x, hx, k, hk, hpow⟩
    by_cases hkzero : k = 0
    · subst k
      have hxy : x = y :=
        doubledAlignedBlackDart_injective homega heta hdegree layer
          (by simpa using hpow)
      simpa [hxy] using hx
    · have hactive : activeBlackDart (omega := omega) (eta := eta)
          ((alignedBoundaryPerm homega heta hdegree layer ^ k)
            (doubledAlignedBlackDart homega heta hdegree layer x)) := by
        rw [hpow]
        exact (doubledAlignedBlackDartEquiv
          homega heta hdegree layer y).2
      exact False.elim ((finiteFirstReturnTime_minimal
        (alignedBoundaryPerm homega heta hdegree layer)
        (activeBlackDart (omega := omega) (eta := eta))
        (doubledAlignedBlackDartEquiv
          homega heta hdegree layer x) k hk)
          ⟨Nat.pos_of_ne_zero hkzero, hactive⟩)
  · intro hy
    refine ⟨y, hy, 0, finiteFirstReturnTime_pos
      (alignedBoundaryPerm homega heta hdegree layer)
      (activeBlackDart (omega := omega) (eta := eta))
      (doubledAlignedBlackDartEquiv
        homega heta hdegree layer y), ?_⟩
    simp

theorem length_doubledAlignedBoundarySegments_eq_layers
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (states : List (DoubledAlignedState omega eta)) :
    (doubledAlignedBoundarySegments homega heta hdegree false states).length =
      (doubledAlignedBoundarySegments
        homega heta hdegree true states).length := by
  classical
  induction states with
  | nil => simp [doubledAlignedBoundarySegments,
      finiteFirstReturnSegments]
  | cons x states ih =>
      simp only [doubledAlignedBoundarySegments,
        finiteFirstReturnSegments, List.map_cons, List.flatMap_cons,
        List.length_append, length_finiteFirstReturnSegment]
      rw [alignedFirstReturnTime_eq homega heta hdegree x]
      exact congrArg
        (fun n => finiteFirstReturnTime
            (alignedBoundaryPerm homega heta hdegree true)
            (activeBlackDart (omega := omega) (eta := eta))
            (doubledAlignedBlackDartEquiv
              homega heta hdegree true x) + n) ih


end StatMech.FrontierD
