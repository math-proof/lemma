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
import Def.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part20
open StatMech.FrontierD


namespace ScratchLocalRetieC

@[simp] theorem doubledAlignedFirstReturnPerm_false_arrival
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    doubledAlignedBlackDartEquiv homega heta hdegree false
        (doubledAlignedFirstReturnPerm homega heta hdegree x) =
      finiteFirstReturn
        (alignedBoundaryPerm homega heta hdegree false)
        (activeBlackDart (omega := omega) (eta := eta))
        (doubledAlignedBlackDartEquiv
          homega heta hdegree false x) := by
  classical
  simp [doubledAlignedFirstReturnPerm]

theorem doubledAlignedFirstReturnPerm_true_common_arrival
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    (finiteFirstReturn
        (alignedBoundaryPerm homega heta hdegree true)
        (activeBlackDart (omega := omega) (eta := eta))
        (doubledAlignedBlackDartEquiv
          homega heta hdegree true x)).1 =
      (doubledAlignedBlackDartEquiv homega heta hdegree false
        (doubledAlignedFirstReturnPerm homega heta hdegree x)).1 := by
  classical
  rw [doubledAlignedFirstReturnPerm_false_arrival]
  exact (alignedFirstReturn_common_arrival
    homega heta hdegree x).symm


theorem exists_aligned_chunk_split_of_flatten_eq_append
    {A : Type*} (chunks : List (List A))
    (hchunks : chunks ≠ [])
    (hnonempty : forall chunk, chunk ∈ chunks -> chunk ≠ [])
    (left right : List A) (hsplit : chunks.flatten = left ++ right) :
    exists before chunk after chunkLeft chunkRight,
      chunks = before ++ chunk :: after /\
        chunk = chunkLeft ++ chunkRight /\
        left = before.flatten ++ chunkLeft /\
        right = chunkRight ++ after.flatten := by
  induction chunks generalizing left right with
  | nil => exact False.elim (hchunks rfl)
  | cons chunk chunks ih =>
      have hchunk : chunk ≠ [] := hnonempty chunk (by simp)
      have htailNonempty : forall c, c ∈ chunks -> c ≠ [] := by
        intro c hc
        exact hnonempty c (by simp [hc])
      simp only [List.flatten_cons] at hsplit
      rcases List.append_eq_append_iff.mp hsplit with hlong | hshort
      · obtain ⟨tailLeft, hleft, htail⟩ := hlong
        by_cases hnil : chunks = []
        · subst chunks
          have hlen := congrArg List.length htail
          simp only [List.flatten_nil, List.length_nil,
            List.length_append] at hlen
          have htailLeftNil : tailLeft = [] :=
            List.length_eq_zero_iff.mp (by omega)
          have hrightNil : right = [] :=
            List.length_eq_zero_iff.mp (by omega)
          subst tailLeft
          subst right
          exact ⟨[], chunk, [], chunk, [], by simp, by simp,
            by simpa using hleft, by simp⟩
        · obtain ⟨before, cut, after, cutLeft, cutRight,
              hchunks', hcut, htailLeft, hright⟩ :=
            ih hnil htailNonempty tailLeft right htail
          exact ⟨chunk :: before, cut, after, cutLeft, cutRight,
            by simp [hchunks'], hcut, by simp [hleft, htailLeft], hright⟩
      · obtain ⟨chunkRight, hchunkSplit, hright⟩ := hshort
        exact ⟨[], chunk, chunks, left, chunkRight,
          by simp, hchunkSplit, by simp, hright⟩

end ScratchLocalRetieC
