/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


@[simp] theorem mem_canonicalMaskRightImages_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p)
    (q : rightMaskFiber ends m j k l zero p) :
    q ∈ canonicalMaskRightImages ends m j k l zero p c ↔
      ∃ r : leftMaskFiber ends m j k l zero p,
        CanonicalTransferWorks ends m k zero r.1.1 c.1.1 ∧
          q.1.1 = balancedSwap m
            (canonicalMiddleTransfer ends m r.1.1 k zero)
            (canonicalOuterTransfer ends m r.1.1 k zero) c.1.1 := by
  classical
  simp [canonicalMaskRightImages]


theorem canonicalMaskRightImages_nonempty
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    (canonicalMaskRightImages ends m j k l zero p c).Nonempty := by
  let q := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p c c
      (canonicalTransferWorks_self hloop hjk hkl hk0 c)
  refine ⟨q, (mem_canonicalMaskRightImages_iff
    ends m j k l zero p c q).mpr ⟨c,
      canonicalTransferWorks_self hloop hjk hkl hk0 c, ?_⟩⟩
  rfl


theorem rightMaskFiber_rowClass_zero_injective
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Function.Injective (fun q : rightMaskFiber ends m j k l zero p =>
      rowClass m q.1.1 0) := by
  intro q r hqr
  apply Subtype.ext
  apply Subtype.ext
  apply eq_of_rowClass_zero_of_fourColorMaskProfile_eq m q.1.1 r.1.1
  · exact q.2.trans r.2.symm
  · exact hqr


theorem leftMaskFiber_rowClass_zero_injective
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Function.Injective (fun c : leftMaskFiber ends m j k l zero p =>
      rowClass m c.1.1 0) := by
  intro c d hcd
  apply Subtype.ext
  apply Subtype.ext
  apply eq_of_rowClass_zero_of_fourColorMaskProfile_eq m c.1.1 d.1.1
  · exact c.2.trans d.2.symm
  · exact hcd


theorem rowClass_zero_canonicalTransferMapOfWorks
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (a c : leftMaskFiber ends m j k l zero p)
    (hworks : CanonicalTransferWorks ends m k zero a.1.1 c.1.1) :
    rowClass m (canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p a c hworks).1.1 0 =
        canonicalTranslatedRow ends m k zero a.1.1 c.1.1 := by
  have hv := canonicalTransfers_valid_on_sameMask hloop hjk hkl a c
  change rowClass m
    (balancedSwap m
      (canonicalMiddleTransfer ends m a.1.1 k zero)
      (canonicalOuterTransfer ends m a.1.1 k zero) c.1.1) 0 = _
  rw [rowClass_balancedSwap_zero hv.1 hv.2.1]
  rfl


end StatMech.GrahamGHS.FourColor
