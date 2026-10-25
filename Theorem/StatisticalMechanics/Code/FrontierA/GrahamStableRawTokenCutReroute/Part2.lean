/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Structure.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalStableRawExceptionalEdge_eq_of_source_target_eq
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p}
    (hsource : s.source = t.source) (htarget : s.target = t.target) :
    s = t := by
  cases s
  cases t
  simp_all


theorem canonicalStableRawExceptionalEdge_source_ne_or_eq_of_target_eq
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (htarget : s.target = t.target) :
    s.source ≠ t.source ∨ s = t := by
  by_cases hsource : s.source = t.source
  · exact Or.inr
      (canonicalStableRawExceptionalEdge_eq_of_source_target_eq hsource htarget)
  · exact Or.inl hsource


theorem exists_canonicalStableRawExceptionalEdge_of_distinct_commonTarget
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c d : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (target : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (hcd : c ≠ d)
    (hc : CanonicalRawGateRelated ends m j k l zero p c.1 target.1)
    (hd : CanonicalRawGateRelated ends m j k l zero p d.1 target.1) :
    ∃ s : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p,
      s.target = target ∧ (s.source = c ∨ s.source = d) := by
  classical
  by_cases hcExceptional : c.1 ≠ canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p target
  · exact ⟨⟨c, target, hc, hcExceptional⟩, rfl, Or.inl rfl⟩
  · have hcOwner : c.1 = canonicalStableRawPreferredRightBase
        ends m j k l zero hloop hjk hkl hk0 p target :=
      Classical.not_not.mp hcExceptional
    have hdExceptional : d.1 ≠ canonicalStableRawPreferredRightBase
        ends m j k l zero hloop hjk hkl hk0 p target := by
      intro hdOwner
      apply hcd
      apply Subtype.ext
      exact hcOwner.trans hdOwner.symm
    exact ⟨⟨d, target, hd, hdExceptional⟩, rfl, Or.inr rfl⟩

end StatMech.GrahamGHS.FourColor
