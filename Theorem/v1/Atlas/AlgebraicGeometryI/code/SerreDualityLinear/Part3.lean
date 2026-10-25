/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityLinear.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicGeometryI.code.CohomologyP1.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CohomologyP1
import Def.v1.Atlas.AlgebraicGeometryI.code.SerreDualityLinear.Part3


namespace SerreDualityP1

open CohomologyP1


/-- The underlying linear map of `shiftEquiv` is `shiftMap`. -/
theorem shiftEquiv_coe_eq (k : Type*) [Field k] :
    (shiftEquiv k : (ℤ →₀ k) →ₗ[k] (ℤ →₀ k)) = shiftMap k := by
  ext f; simp [shiftEquiv, shiftMap, LinearEquiv.ofInvolutive]


/-- The residue shift sends the open interval `(n, 0)` bijectively onto `[0, -2 - n]`. -/
theorem residueShift_image_Ioo (n : ℤ) :
    residueShift '' (Set.Ioo n 0) = Set.Icc 0 (-2 - n) := by
  ext x
  simp only [Set.mem_image, Set.mem_Ioo, Set.mem_Icc, residueShift]
  constructor
  · rintro ⟨y, ⟨hyn, hy0⟩, rfl⟩; constructor <;> omega
  · intro ⟨hx0, hxn⟩; exact ⟨-1 - x, ⟨by omega, by omega⟩, by omega⟩

/-- `shiftMap` carries Laurent polynomials supported on `(n, 0)` to those supported on `[0, -2 - n]`. -/
theorem shiftMap_supported_Ioo (k : Type*) [Field k] (n : ℤ) :
    Submodule.map (shiftMap k) (Finsupp.supported k k (Set.Ioo n 0)) =
    Finsupp.supported k k (Set.Icc 0 (-2 - n)) := by
  rw [shiftMap, Finsupp.lmapDomain_supported, residueShift_image_Ioo]


end SerreDualityP1
