/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part7
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalMaskRightAugmentedAssignedRows_contains
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S T : Finset (leftMaskFiber ends m j k l zero p))
    (hTS : T ⊆ S)
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (u : ↑S) (huT : u.1 ∈ T) (huc : u ≠ c) :
    ∃ qS : ↑(canonicalMaskRightNeighborhood
        ends m j k l zero p S),
      f u = some qS ∧ qS.1 ∈ canonicalMaskRightAugmentedAssignedRows
        ends m j k l zero p S T hTS c f hf := by
  classical
  let qS := canonicalMaskRightAugmentedAssignedImage
    ends m j k l zero p S c f hf u huc
  refine ⟨qS, canonicalMaskRightAugmentedAssignedImage_apply
    ends m j k l zero p S c f hf u huc, ?_⟩
  have huErase : u.1 ∈ T.erase c.1 := Finset.mem_erase.mpr ⟨by
    intro h
    exact huc (Subtype.ext h), huT⟩
  let x : ↑(T.erase c.1) := ⟨u.1, huErase⟩
  rw [canonicalMaskRightAugmentedAssignedRows]
  apply Finset.mem_image.mpr
  refine ⟨x, Finset.mem_attach _ _, ?_⟩
  let xS : ↑S := ⟨x.1, hTS (Finset.mem_of_mem_erase x.2)⟩
  have hxc : xS ≠ c := by
    intro h
    exact (Finset.mem_erase.mp x.2).1 (congrArg Subtype.val h)
  have hxS : xS = u :=
    Subtype.ext rfl
  change (canonicalMaskRightAugmentedAssignedImage
    ends m j k l zero p S c f hf xS hxc).1 = qS.1
  apply congrArg Subtype.val
  apply Option.some.inj
  calc
    some (canonicalMaskRightAugmentedAssignedImage
        ends m j k l zero p S c f hf xS hxc) = f xS :=
      (canonicalMaskRightAugmentedAssignedImage_apply
        ends m j k l zero p S c f hf xS hxc).symm
    _ = f u := congrArg f hxS
    _ = some qS := canonicalMaskRightAugmentedAssignedImage_apply
      ends m j k l zero p S c f hf u huc

theorem card_canonicalMaskRightAugmentedAssignedRows
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S T : Finset (leftMaskFiber ends m j k l zero p))
    (hTS : T ⊆ S)
    (c : ↑S) (hcT : c.1 ∈ T)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f) :
    (canonicalMaskRightAugmentedAssignedRows
      ends m j k l zero p S T hTS c f hf).card + 1 = T.card := by
  classical
  let g : ↑(T.erase c.1) -> rightMaskFiber ends m j k l zero p := fun x =>
    (canonicalMaskRightAugmentedAssignedImage
      ends m j k l zero p S c f hf
      ⟨x.1, hTS (Finset.mem_of_mem_erase x.2)⟩ (by
        intro h
        exact (Finset.mem_erase.mp x.2).1 (congrArg Subtype.val h))).1
  have hg : Function.Injective g := by
    intro x y hxy
    let xS : ↑S := ⟨x.1, hTS (Finset.mem_of_mem_erase x.2)⟩
    let yS : ↑S := ⟨y.1, hTS (Finset.mem_of_mem_erase y.2)⟩
    have hxc : xS ≠ c := by
      intro h
      exact (Finset.mem_erase.mp x.2).1 (congrArg Subtype.val h)
    have hyc : yS ≠ c := by
      intro h
      exact (Finset.mem_erase.mp y.2).1 (congrArg Subtype.val h)
    let qx := canonicalMaskRightAugmentedAssignedImage
      ends m j k l zero p S c f hf xS hxc
    let qy := canonicalMaskRightAugmentedAssignedImage
      ends m j k l zero p S c f hf yS hyc
    have hq : qx = qy := Subtype.ext hxy
    have hfx := canonicalMaskRightAugmentedAssignedImage_apply
      ends m j k l zero p S c f hf xS hxc
    have hfy := canonicalMaskRightAugmentedAssignedImage_apply
      ends m j k l zero p S c f hf yS hyc
    have hfxy : f xS = f yS := calc
      f xS = some qx := hfx
      _ = some qy := congrArg some hq
      _ = f yS := hfy.symm
    have hxyS : xS = yS := f.injective hfxy
    apply Subtype.ext
    exact congrArg (fun z : ↑S => z.1) hxyS
  have hpos : 0 < T.card := Finset.card_pos.mpr ⟨c.1, hcT⟩
  change (Finset.image g (T.erase c.1).attach).card + 1 = T.card
  rw [Finset.card_image_of_injective _ hg, Finset.card_attach,
    Finset.card_erase_of_mem hcT]
  omega

theorem canonicalMaskRightAugmentedAssignedRows_subset_neighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S T : Finset (leftMaskFiber ends m j k l zero p))
    (hTS : T ⊆ S)
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f) :
    canonicalMaskRightAugmentedAssignedRows
        ends m j k l zero p S T hTS c f hf ⊆
      canonicalMaskRightNeighborhood ends m j k l zero p T := by
  classical
  intro q hq
  rw [canonicalMaskRightAugmentedAssignedRows] at hq
  obtain ⟨x, -, hqx⟩ := Finset.mem_image.mp hq
  have hxT : x.1 ∈ T := Finset.mem_of_mem_erase x.2
  have hxS : x.1 ∈ S := hTS hxT
  let xS : ↑S := ⟨x.1, hxS⟩
  have hxc : xS ≠ c := by
    intro h
    exact (Finset.mem_erase.mp x.2).1 (congrArg Subtype.val h)
  have hmem := canonicalMaskRightAugmentedAssignedImage_mem
    ends m j k l zero p S c f hf xS hxc
  apply (mem_canonicalMaskRightNeighborhood_iff
    ends m j k l zero p T q).mpr
  refine ⟨x.1, hxT, ?_⟩
  rw [← hqx]
  exact hmem


theorem canonicalMaskRightAugmentedAssignedRows_full_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (htight : (canonicalMaskRightNeighborhood
        ends m j k l zero p S).card + 1 = S.card)
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f) :
    canonicalMaskRightAugmentedAssignedRows ends m j k l zero p
        S S Finset.Subset.rfl c f hf =
      canonicalMaskRightNeighborhood ends m j k l zero p S := by
  classical
  apply Finset.eq_of_subset_of_card_le
    (canonicalMaskRightAugmentedAssignedRows_subset_neighborhood
      ends m j k l zero p S S Finset.Subset.rfl c f hf)
  have hcard := card_canonicalMaskRightAugmentedAssignedRows
    ends m j k l zero p S S Finset.Subset.rfl c c.2 f hf
  omega


end StatMech.GrahamGHS.FourColor
