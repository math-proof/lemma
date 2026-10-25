/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalEdgeDegreeHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightRootCutHallEquivalence
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalEdgeDegreeHall.Part5
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def CanonicalMaskRightSelectedOppositeClosure
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ c : leftMaskFiber ends m j k l zero p,
    ∀ q : rightMaskFiber ends m j k l zero p,
      q ∈ canonicalMaskRightImages ends m j k l zero p c ->
        ∀ d : {d : leftMaskFiber ends m j k l zero p //
          q ∈ canonicalMaskRightImages ends m j k l zero p d},
          CanonicalTransferWorks ends m k zero
            (canonicalMaskRightPreimageReference
              ends m j k l zero p q d).1.1 c.1.1


noncomputable def canonicalMaskRightEdgePreimageEmbedding_of_selectedOppositeClosure
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (hclose : CanonicalMaskRightSelectedOppositeClosure
      ends m j k l zero p) :
    CanonicalMaskRightEdgePreimageEmbedding ends m j k l zero p := by
  intro c q hqc
  let source := {d : leftMaskFiber ends m j k l zero p //
    q ∈ canonicalMaskRightImages ends m j k l zero p d}
  let target := {r : rightMaskFiber ends m j k l zero p //
    r ∈ canonicalMaskRightImages ends m j k l zero p c}
  let ref : source -> leftMaskFiber ends m j k l zero p := fun d =>
    canonicalMaskRightPreimageReference ends m j k l zero p q d
  let works : ∀ d : source,
      CanonicalTransferWorks ends m k zero (ref d).1.1 c.1.1 := fun d =>
    hclose c q hqc d
  let f : source -> target := fun d =>
    ⟨canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p (ref d) c (works d),
      (mem_canonicalMaskRightImages_iff
        ends m j k l zero p c _).mpr ⟨ref d, works d, rfl⟩⟩
  refine ⟨⟨f, ?_⟩⟩
  intro d e hde
  have hrawC := congrArg (fun z : target => z.1.1.1) hde
  have hrowC := (canonicalBalancedSwaps_eq_iff_rowSymmDiff
    hloop hjk hkl (ref d) (ref e) c c).mp hrawC
  have htransfer : canonicalTransferUnion ends m k zero (ref d).1.1 =
      canonicalTransferUnion ends m k zero (ref e).1.1 := by
    have h := congrArg (fun K : Finset I =>
      (rowClass m c.1.1 0) ∆ K) hrowC
    simpa [symmDiff_assoc] using h
  have hrawD : balancedSwap m
        (canonicalMiddleTransfer ends m (ref d).1.1 k zero)
        (canonicalOuterTransfer ends m (ref d).1.1 k zero) d.1.1.1 =
      balancedSwap m
        (canonicalMiddleTransfer ends m (ref e).1.1 k zero)
        (canonicalOuterTransfer ends m (ref e).1.1 k zero) e.1.1.1 :=
    (canonicalMaskRightPreimageReference_eq
      ends m j k l zero p q d).symm.trans
        (canonicalMaskRightPreimageReference_eq
          ends m j k l zero p q e)
  have hrowD := (canonicalBalancedSwaps_eq_iff_rowSymmDiff
    hloop hjk hkl (ref d) (ref e) d.1 e.1).mp hrawD
  rw [htransfer] at hrowD
  have hsupport : rowClass m d.1.1.1 0 = rowClass m e.1.1.1 0 := by
    have h := congrArg (fun K : Finset I =>
      K ∆ (canonicalTransferUnion ends m k zero (ref e).1.1)) hrowD
    simpa [symmDiff_assoc] using h
  apply Subtype.ext
  exact leftMaskFiber_rowClass_zero_injective
    ends m j k l zero p hsupport


end StatMech.GrahamGHS.FourColor
