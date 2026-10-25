/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part9
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def CanonicalMaskRightSecondCommonDisplacement
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c d : ↑S)
    (ef : canonicalMaskRightAugmentedEquivType
          ends m j k l zero p S ×
        canonicalMaskRightAugmentedEquivType ends m j k l zero p S) : Prop :=
  let σ : Equiv.Perm ↑S := ef.1.trans ef.2.symm
  ∀ x : ↑S, x ≠ c ->
    ∃ q : rightMaskFiber ends m j k l zero p,
      q ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
      q ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1 ∧
      ∀ r : rightMaskFiber ends m j k l zero p, r ≠ q ->
        r ∈ canonicalMaskRightImages ends m j k l zero p x.1 ->
        r ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1 ->
        ∃ u v : ↑S,
          u ≠ c ∧ v ≠ d ∧ u ≠ x ∧ v ≠ σ x ∧ σ u = v ∧
            r ∈ canonicalMaskRightImages ends m j k l zero p u.1 ∧
            r ∈ canonicalMaskRightImages ends m j k l zero p v.1


noncomputable def canonicalPermMovedCard
    {A : Type*} [Fintype A] (σ : Equiv.Perm A) : Nat := by
  classical
  exact (Finset.univ.filter fun x => σ x ≠ x).card

end StatMech.GrahamGHS.FourColor
