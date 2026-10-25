/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Instance.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalStableRawExceptionalEdgeEquivRightCollisionToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I) :
    let T := canonicalRawCommonClosure ends m j k l zero p
    let R := CanonicalRawGateRelated ends m j k l zero p
    let U := StatMech.FrontierA.finiteRelationNeighborhood R T
    let rightBase := canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p
    letI : DecidableEq (leftSourceMaskFiber ends m j k l zero p) :=
      Classical.decEq _
    letI : DecidableRel R := Classical.decRel R
    CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p ≃
      StatMech.FrontierA.bipartiteRightCollisionToken
        R T U rightBase := by
  classical
  dsimp only
  let T := canonicalRawCommonClosure ends m j k l zero p
  let R := CanonicalRawGateRelated ends m j k l zero p
  let U := StatMech.FrontierA.finiteRelationNeighborhood R T
  let rightBase := canonicalStableRawPreferredRightBase
    ends m j k l zero hloop hjk hkl hk0 p
  let E := CanonicalStableRawExceptionalEdge
    ends m j k l zero hloop hjk hkl hk0 p
  let forward : E → StatMech.FrontierA.bipartiteRightCollisionToken
      R T U rightBase := fun s =>
    ⟨s.target, ⟨s.source.1, Finset.mem_erase.mpr
      ⟨s.exceptional, Finset.mem_filter.mpr ⟨s.source.2, s.related⟩⟩⟩⟩
  let inverse : StatMech.FrontierA.bipartiteRightCollisionToken
      R T U rightBase → E := fun token =>
    ⟨⟨token.2.1, (Finset.mem_filter.mp
        (Finset.mem_of_mem_erase token.2.2)).1⟩,
      token.1,
      (Finset.mem_filter.mp (Finset.mem_of_mem_erase token.2.2)).2,
      Finset.ne_of_mem_erase token.2.2⟩
  refine ⟨forward, inverse, ?_, ?_⟩
  · intro s
    cases s
    rfl
  · intro token
    rcases token with ⟨target, source, hsource⟩
    rfl


def CanonicalStableRawNoOpposingCuts
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I) : Prop :=
  ∀ s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p,
    let hc := canonicalRawCommonClosure_leftGate
      ends m j k l zero p s.source.1 s.source.2
    let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
      ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p s.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p s.target⟩
    let hb := canonicalRawCommonClosure_leftGate
      ends m j k l zero p b.1 b.2
    let a := sourceMaskGatePointToLeftMaskFiber
      ends m j k l zero p s.source.1 hc
    let owner := sourceMaskGatePointToLeftMaskFiber
      ends m j k l zero p b.1 hb
    let q := (rightMaskFiberEquivReversedSourceMaskGateFiber
      ends m j k l zero p).symm
        ⟨s.target.1, s.related.choose_spec.1⟩
    ¬ CanonicalOpposingRootCutsAtRight
      ends m j k l zero p a owner q


end StatMech.GrahamGHS.FourColor
