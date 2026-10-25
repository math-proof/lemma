/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem exists_canonicalStableRawExceptionalEdge_next
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    ∃ t : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p,
      let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p s.target,
        canonicalStableRawPreferredRightBase_mem ends m j k l zero
          hloop hjk hkl hk0 p s.target⟩
      t.target.1 ≠ s.target.1 ∧
        CanonicalRawGateRelated ends m j k l zero p
          s.source.1 t.target.1 ∧
        CanonicalRawGateRelated ends m j k l zero p b.1 t.target.1 ∧
        (t.source = s.source ∨ t.source = b) ∧
        (t.source = b ∨
          (t.source = s.source ∧
            canonicalStableRawPreferredRightBase
              ends m j k l zero hloop hjk hkl hk0 p t.target = b.1)) := by
  classical
  let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
      hloop hjk hkl hk0 p s.target,
    canonicalStableRawPreferredRightBase_mem ends m j k l zero
      hloop hjk hkl hk0 p s.target⟩
  rcases canonicalStableOccupiedAlternate_opposingCuts_or_distinctReroute
      ends m j k l zero hloop hjk hkl hk0 p s.source s.target
        s.related s.exceptional with hcuts | ⟨e, hse, hbe, hes⟩
  · exact False.elim (hno s hcuts)
  · have heMem : e ∈ StatMech.FrontierA.finiteRelationNeighborhood
        (CanonicalRawGateRelated ends m j k l zero p)
        (canonicalRawCommonClosure ends m j k l zero p) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ e,
        s.source.1, s.source.2, hse⟩
    let eTarget : ↑(StatMech.FrontierA.finiteRelationNeighborhood
        (CanonicalRawGateRelated ends m j k l zero p)
        (canonicalRawCommonClosure ends m j k l zero p)) := ⟨e, heMem⟩
    by_cases hbExceptional : b.1 ≠
        canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p eTarget
    · exact ⟨⟨b, eTarget, hbe, hbExceptional⟩,
        hes, hse, hbe, Or.inr rfl, Or.inl rfl⟩
    · have hsExceptional : s.source.1 ≠
          canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p eTarget := by
        intro hsBase
        apply s.exceptional
        exact hsBase.trans (Classical.not_not.mp hbExceptional).symm
      exact ⟨⟨s.source, eTarget, hse, hsExceptional⟩,
        hes, hse, hbe, Or.inl rfl, Or.inr ⟨rfl,
          (Classical.not_not.mp hbExceptional).symm⟩⟩


end StatMech.GrahamGHS.FourColor
