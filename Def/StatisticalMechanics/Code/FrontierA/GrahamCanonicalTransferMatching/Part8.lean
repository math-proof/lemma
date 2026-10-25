/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part7
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalMaskRightAugmentedAssignedEquiv
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f) :
    {u : ↑S // u ≠ c} ≃
      ↑(canonicalMaskRightNeighborhood ends m j k l zero p S) := by
  classical
  let g : {u : ↑S // u ≠ c} ->
      ↑(canonicalMaskRightNeighborhood ends m j k l zero p S) := fun u =>
    canonicalMaskRightAugmentedAssignedImage
      ends m j k l zero p S c f hf u.1 u.2
  have hinj : Function.Injective g := by
    intro u v huv
    apply Subtype.ext
    apply f.injective
    calc
      f u.1 = some (g u) := canonicalMaskRightAugmentedAssignedImage_apply
        ends m j k l zero p S c f hf u.1 u.2
      _ = some (g v) := congrArg some huv
      _ = f v.1 := (canonicalMaskRightAugmentedAssignedImage_apply
        ends m j k l zero p S c f hf v.1 v.2).symm
  have hsurj : Function.Surjective g := by
    intro q
    let x : ↑S := f.symm (some q)
    have hxc : x ≠ c := by
      intro h
      have happly : f x = some q := by simp [x]
      rw [h, hf.1] at happly
      simp at happly
    let u : {u : ↑S // u ≠ c} := ⟨x, hxc⟩
    refine ⟨u, ?_⟩
    apply Option.some.inj
    calc
      some (g u) = f x := (canonicalMaskRightAugmentedAssignedImage_apply
        ends m j k l zero p S c f hf x hxc).symm
      _ = some q := by simp [x]
  exact Equiv.ofBijective g ⟨hinj, hsurj⟩


end StatMech.GrahamGHS.FourColor
