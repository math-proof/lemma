/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityLinear.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CohomologyP1
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CohomologyP1

namespace SerreDualityP1

open CohomologyP1


/-- The residue shift `i ↦ -1 - i` realizing the duality at the index level. -/
def residueShift : ℤ → ℤ := fun i => -1 - i

/-- The composition `residueShift ∘ residueShift` equals the identity. -/
theorem residueShift_comp_self : residueShift ∘ residueShift = id := by
  funext i; simp [residueShift]


/-- The `k`-linear map on `ℤ →₀ k` induced by the residue shift `i ↦ -1 - i`. -/
noncomputable def shiftMap (k : Type*) [Field k] : (ℤ →₀ k) →ₗ[k] (ℤ →₀ k) :=
  Finsupp.lmapDomain k k residueShift

/-- The `shiftMap` is involutive, inherited from `residueShift`. -/
theorem shiftMap_involutive (k : Type*) [Field k] :
    Function.Involutive (shiftMap k) := by
  intro f
  show Finsupp.mapDomain residueShift (Finsupp.mapDomain residueShift f) = f
  rw [← Finsupp.mapDomain_comp (f := residueShift) (g := residueShift),
      residueShift_comp_self, Finsupp.mapDomain_id]

/-- The `k`-linear involution `(ℤ →₀ k) ≃ₗ[k] (ℤ →₀ k)` induced by the residue shift. -/
noncomputable def shiftEquiv (k : Type*) [Field k] : (ℤ →₀ k) ≃ₗ[k] (ℤ →₀ k) :=
  LinearEquiv.ofInvolutive (shiftMap k) (shiftMap_involutive k)

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


/-- `shiftEquiv` restricted to supports on `(n, 0)` is a linear isomorphism
onto supports on `[0, -2 - n]`. -/
noncomputable def shiftEquiv_supported (k : Type*) [Field k] (n : ℤ) :
    ↥(Finsupp.supported k k (Set.Ioo n 0)) ≃ₗ[k]
    ↥(Finsupp.supported k k (Set.Icc 0 (-2 - n))) := by
  have e := (shiftEquiv k).submoduleMap (Finsupp.supported k k (Set.Ioo n 0))
  rwa [shiftEquiv_coe_eq, shiftMap_supported_Ioo] at e


/-- Serre duality on `ℙ¹` as a linear isomorphism: for `n < -1`,
`H¹(O(n)) ≅ H⁰(O(-2 - n))` via the residue shift. -/
noncomputable def serre_duality_P1 (k : Type) [Field k] (n : ℤ) (_hn : n < -1) :
    ((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k n)) ≃ₗ[k] ↥(CechH0 k (-2 - n)) :=

  (H1_equiv_supported_complement k n) |>.trans

  (shiftEquiv_supported k n) |>.trans

  (LinearEquiv.ofEq _ _ (cechH0_eq_supported k (-2 - n)).symm)
