/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalStableOccupiedAlternate_opposingCuts_or_twoRow
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (hcd : CanonicalRawGateRelated ends m j k l zero p c.1 d.1)
    (hne : c.1 ≠ canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p d) :
    let hc := canonicalRawCommonClosure_leftGate
      ends m j k l zero p c.1 c.2
    let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
      ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p d,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p d⟩
    let hb := canonicalRawCommonClosure_leftGate
      ends m j k l zero p b.1 b.2
    let a := sourceMaskGatePointToLeftMaskFiber
      ends m j k l zero p c.1 hc
    let owner := sourceMaskGatePointToLeftMaskFiber
      ends m j k l zero p b.1 hb
    let q := (rightMaskFiberEquivReversedSourceMaskGateFiber
      ends m j k l zero p).symm ⟨d.1, hcd.choose_spec.1⟩
    CanonicalOpposingRootCutsAtRight
        ends m j k l zero p a owner q ∨
      CanonicalTightTwoRowCollision ends m j k l zero p a owner := by
  classical
  dsimp only
  obtain ⟨hcEdge, hdEdge, hqc⟩ := hcd
  let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
      hloop hjk hkl hk0 p d,
    canonicalStableRawPreferredRightBase_mem ends m j k l zero
      hloop hjk hkl hk0 p d⟩
  let hc := canonicalRawCommonClosure_leftGate
    ends m j k l zero p c.1 c.2
  let hb := canonicalRawCommonClosure_leftGate
    ends m j k l zero p b.1 b.2
  let a := sourceMaskGatePointToLeftMaskFiber
    ends m j k l zero p c.1 hc
  let owner := sourceMaskGatePointToLeftMaskFiber
    ends m j k l zero p b.1 hb
  let q := (rightMaskFiberEquivReversedSourceMaskGateFiber
    ends m j k l zero p).symm ⟨d.1, hdEdge⟩
  have haowner : a ≠ owner := by
    intro h
    apply hne
    apply Subtype.ext
    exact congrArg (fun x => x.1.1) h
  have hqa : q ∈ canonicalMaskRightImages
      ends m j k l zero p a := by
    simpa only [q, a] using hqc
  have hbrel := canonicalStableRawPreferredRightBase_related
    ends m j k l zero hloop hjk hkl hk0 p d
  obtain ⟨hbEdge, hdOwner, hqowner⟩ := hbrel
  have hqo : q ∈ canonicalMaskRightImages
      ends m j k l zero p owner := by
    simpa only [q, owner, b] using hqowner
  exact canonicalCommonImage_opposingAtRight_or_twoCommon
    hloop hjk hkl a owner haowner q hqa hqo


theorem canonicalStableRawRightTarget_memClosure_or_positive
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p))) :
    d.1 ∈ canonicalRawCommonClosure ends m j k l zero p ∨
      ReversalGatePositive ends m j k l zero p d.1 := by
  classical
  obtain ⟨source, hsource, hrelated⟩ :=
    (Finset.mem_filter.mp d.2).2
  obtain ⟨_, hdRight, _⟩ := hrelated
  by_cases hdLeft : RowsDisconnect ends m d.1.1 k zero
  · exact Or.inl
      ((canonicalRawCommonClosure_right_iff_neighborhood_left
        ends m j k l zero p d.1).mpr ⟨d.2, hdLeft⟩).1
  · exact Or.inr ⟨hdLeft, hdRight⟩


theorem canonicalStableOccupiedAlternate_positive_or_commonGeometry
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (hcd : CanonicalRawGateRelated ends m j k l zero p c.1 d.1)
    (hne : c.1 ≠ canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p d) :
    ReversalGatePositive ends m j k l zero p d.1 ∨
      ∃ dCommon : ↑(canonicalRawCommonClosure ends m j k l zero p),
        dCommon.1 = d.1 ∧
        let hc := canonicalRawCommonClosure_leftGate
          ends m j k l zero p c.1 c.2
        let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
          ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p d,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p d⟩
        let hb := canonicalRawCommonClosure_leftGate
          ends m j k l zero p b.1 b.2
        let a := sourceMaskGatePointToLeftMaskFiber
          ends m j k l zero p c.1 hc
        let owner := sourceMaskGatePointToLeftMaskFiber
          ends m j k l zero p b.1 hb
        let q := (rightMaskFiberEquivReversedSourceMaskGateFiber
          ends m j k l zero p).symm ⟨d.1, hcd.choose_spec.1⟩
        CanonicalOpposingRootCutsAtRight
            ends m j k l zero p a owner q ∨
          CanonicalTightTwoRowCollision ends m j k l zero p a owner := by
  rcases canonicalStableRawRightTarget_memClosure_or_positive
      ends m j k l zero p d with hdClosure | hdPositive
  · exact Or.inr ⟨⟨d.1, hdClosure⟩, rfl,
      canonicalStableOccupiedAlternate_opposingCuts_or_twoRow
        ends m j k l zero hloop hjk hkl hk0 p c d hcd hne⟩
  · exact Or.inl hdPositive


theorem canonicalStableOccupiedAlternate_opposingCuts_or_distinctReroute
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (hcd : CanonicalRawGateRelated ends m j k l zero p c.1 d.1)
    (hne : c.1 ≠ canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p d) :
    let hc := canonicalRawCommonClosure_leftGate
      ends m j k l zero p c.1 c.2
    let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
      ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p d,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p d⟩
    let hb := canonicalRawCommonClosure_leftGate
      ends m j k l zero p b.1 b.2
    let a := sourceMaskGatePointToLeftMaskFiber
      ends m j k l zero p c.1 hc
    let owner := sourceMaskGatePointToLeftMaskFiber
      ends m j k l zero p b.1 hb
    let q := (rightMaskFiberEquivReversedSourceMaskGateFiber
      ends m j k l zero p).symm ⟨d.1, hcd.choose_spec.1⟩
    CanonicalOpposingRootCutsAtRight
        ends m j k l zero p a owner q ∨
      ∃ e : leftSourceMaskFiber ends m j k l zero p,
        CanonicalRawGateRelated ends m j k l zero p c.1 e ∧
          CanonicalRawGateRelated ends m j k l zero p b.1 e ∧
          e ≠ d.1 := by
  classical
  dsimp only
  obtain ⟨hcEdge, hdEdge, hqc⟩ := hcd
  let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
      hloop hjk hkl hk0 p d,
    canonicalStableRawPreferredRightBase_mem ends m j k l zero
      hloop hjk hkl hk0 p d⟩
  let hb := canonicalRawCommonClosure_leftGate
    ends m j k l zero p b.1 b.2
  let hc := canonicalRawCommonClosure_leftGate
    ends m j k l zero p c.1 c.2
  let a := sourceMaskGatePointToLeftMaskFiber
    ends m j k l zero p c.1 hc
  let owner := sourceMaskGatePointToLeftMaskFiber
    ends m j k l zero p b.1 hb
  let rawEquiv := rightMaskFiberEquivReversedSourceMaskGateFiber
    ends m j k l zero p
  let q := rawEquiv.symm ⟨d.1, hdEdge⟩
  have haowner : a ≠ owner := by
    intro h
    apply hne
    apply Subtype.ext
    exact congrArg (fun x => x.1.1) h
  have hqa : q ∈ canonicalMaskRightImages
      ends m j k l zero p a := by
    simpa only [q, a, rawEquiv] using hqc
  have hbrel := canonicalStableRawPreferredRightBase_related
    ends m j k l zero hloop hjk hkl hk0 p d
  obtain ⟨hbEdge, hdOwner, hqowner⟩ := hbrel
  have hqo : q ∈ canonicalMaskRightImages
      ends m j k l zero p owner := by
    simpa only [q, owner, b, rawEquiv] using hqowner
  rcases canonicalCommonImage_opposingAtRight_or_twoCommon
      hloop hjk hkl a owner haowner q hqa hqo with hcuts | htwo
  · exact Or.inl hcuts
  · obtain ⟨r, hrq, hra, hrowner⟩ :=
      (exists_secondCommonImage_iff_canonicalTightTwoRowCollision
        ends m j k l zero p a owner q hqa hqo).mpr htwo
    let e := (rawEquiv r).1
    have heRight : RowsDisconnect ends m (middleSwap m e.1) k zero :=
      (rawEquiv r).2
    have hback : rawEquiv.symm ⟨e, heRight⟩ = r := by
      exact rawEquiv.symm_apply_apply r
    refine Or.inr ⟨e, ⟨hcEdge, heRight, ?_⟩,
      ⟨hbEdge, heRight, ?_⟩, ?_⟩
    · rw [hback]
      exact hra
    · rw [hback]
      exact hrowner
    · intro hed
      apply hrq
      apply rawEquiv.injective
      apply Subtype.ext
      change e = (rawEquiv q).1
      rw [rawEquiv.apply_symm_apply]
      exact hed


theorem canonicalStableOccupiedAlternate_cut_or_free_or_sameSourceNext
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (hcd : CanonicalRawGateRelated ends m j k l zero p c.1 d.1)
    (hne : c.1 ≠ canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p d) :
    let hc := canonicalRawCommonClosure_leftGate
      ends m j k l zero p c.1 c.2
    let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
      ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p d,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p d⟩
    let hb := canonicalRawCommonClosure_leftGate
      ends m j k l zero p b.1 b.2
    let a := sourceMaskGatePointToLeftMaskFiber
      ends m j k l zero p c.1 hc
    let owner := sourceMaskGatePointToLeftMaskFiber
      ends m j k l zero p b.1 hb
    let q := (rightMaskFiberEquivReversedSourceMaskGateFiber
      ends m j k l zero p).symm ⟨d.1, hcd.choose_spec.1⟩
    CanonicalOpposingRootCutsAtRight
        ends m j k l zero p a owner q ∨
      ∃ e : ↑(StatMech.FrontierA.finiteRelationNeighborhood
          (CanonicalRawGateRelated ends m j k l zero p)
          (canonicalRawCommonClosure ends m j k l zero p)),
        e.1 ≠ d.1 ∧
          CanonicalRawGateRelated ends m j k l zero p c.1 e.1 ∧
          (canonicalStableRawPreferredRightBase
                ends m j k l zero hloop hjk hkl hk0 p e = c.1 ∨
            c.1 ≠ canonicalStableRawPreferredRightBase
              ends m j k l zero hloop hjk hkl hk0 p e) := by
  classical
  dsimp only
  rcases canonicalStableOccupiedAlternate_opposingCuts_or_distinctReroute
      ends m j k l zero hloop hjk hkl hk0 p c d hcd hne with
    hcuts | ⟨e, hce, _, hed⟩
  · exact Or.inl hcuts
  · have heMem : e ∈ StatMech.FrontierA.finiteRelationNeighborhood
        (CanonicalRawGateRelated ends m j k l zero p)
        (canonicalRawCommonClosure ends m j k l zero p) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, c.1, c.2, hce⟩
    let eTarget : ↑(StatMech.FrontierA.finiteRelationNeighborhood
        (CanonicalRawGateRelated ends m j k l zero p)
        (canonicalRawCommonClosure ends m j k l zero p)) := ⟨e, heMem⟩
    by_cases hfree : canonicalStableRawPreferredRightBase
        ends m j k l zero hloop hjk hkl hk0 p eTarget = c.1
    · exact Or.inr ⟨eTarget, hed, hce, Or.inl hfree⟩
    · exact Or.inr ⟨eTarget, hed, hce, Or.inr (fun h => hfree h.symm)⟩


end StatMech.GrahamGHS.FourColor
