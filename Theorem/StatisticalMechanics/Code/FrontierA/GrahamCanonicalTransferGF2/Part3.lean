/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferGF2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCoverageJoin.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferGF2.Part2
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalMaskTransferAdjacent_iff_exists_works_rowSymmDiff
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (c d : leftMaskFiber ends m j k l zero p) :
    CanonicalMaskTransferAdjacent ends m j k l zero p c d ↔
      ∃ a b : leftMaskFiber ends m j k l zero p,
        CanonicalTransferWorks ends m k zero a.1.1 c.1.1 ∧
          CanonicalTransferWorks ends m k zero b.1.1 d.1.1 ∧
          rowClass m c.1.1 0 ∆
              canonicalTransferUnion ends m k zero a.1.1 =
            rowClass m d.1.1 0 ∆
              canonicalTransferUnion ends m k zero b.1.1 := by
  constructor
  · rintro ⟨q, a, b, hqc, hqd⟩
    refine ⟨a, b, ?_, ?_, ?_⟩
    · rw [CanonicalTransferWorks, ← hqc]
      exact q.1.2.2.2.2.2
    · rw [CanonicalTransferWorks, ← hqd]
      exact q.1.2.2.2.2.2
    · apply (canonicalBalancedSwaps_eq_iff_rowSymmDiff
        hloop hjk hkl a b c d).mp
      exact hqc.symm.trans hqd
  · rintro ⟨a, b, hac, hbd, hrow⟩
    let q := canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p a c hac
    refine ⟨q, a, b, rfl, ?_⟩
    change balancedSwap m
        (canonicalMiddleTransfer ends m a.1.1 k zero)
        (canonicalOuterTransfer ends m a.1.1 k zero) c.1.1 =
      balancedSwap m
        (canonicalMiddleTransfer ends m b.1.1 k zero)
        (canonicalOuterTransfer ends m b.1.1 k zero) d.1.1
    exact (canonicalBalancedSwaps_eq_iff_rowSymmDiff
      hloop hjk hkl a b c d).mpr hrow


theorem canonicalMaskTransferAdjacent_iff_exists_translatedRow
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (c d : leftMaskFiber ends m j k l zero p) :
    CanonicalMaskTransferAdjacent ends m j k l zero p c d ↔
      ∃ a b : leftMaskFiber ends m j k l zero p,
        RowSupportDisconnects ends m
            (canonicalTranslatedRow ends m k zero a.1.1 c.1.1) k zero ∧
          canonicalTranslatedRow ends m k zero a.1.1 c.1.1 =
            canonicalTranslatedRow ends m k zero b.1.1 d.1.1 := by
  rw [canonicalMaskTransferAdjacent_iff_exists_works_rowSymmDiff
    hloop hjk hkl c d]
  constructor
  · rintro ⟨a, b, hac, -, heq⟩
    exact ⟨a, b,
      (canonicalTransferWorks_iff_translatedRowDisconnects
        hloop hjk hkl a c).mp hac,
      heq⟩
  · rintro ⟨a, b, hdisc, heq⟩
    have hac := (canonicalTransferWorks_iff_translatedRowDisconnects
      hloop hjk hkl a c).mpr hdisc
    have hbd : CanonicalTransferWorks ends m k zero b.1.1 d.1.1 :=
      (canonicalTransferWorks_iff_translatedRowDisconnects
        hloop hjk hkl b d).mpr (heq ▸ hdisc)
    exact ⟨a, b, hac, hbd, heq⟩


theorem mem_canonicalMaskOrbitCoverage_iff_translatedRow
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r d : leftMaskFiber ends m j k l zero p) :
    d ∈ canonicalMaskOrbitCoverage ends m j k l zero p r ↔
      CanonicalMaskTransferOrbit ends m j k l zero p r d ∧
        RowSupportDisconnects ends m
          (canonicalTranslatedRow ends m k zero r.1.1 d.1.1) k zero := by
  rw [mem_canonicalMaskOrbitCoverage_iff]
  exact and_congr_right fun _ =>
    canonicalTransferWorks_iff_translatedRowDisconnects
      hloop hjk hkl r d

end StatMech.GrahamGHS.FourColor
