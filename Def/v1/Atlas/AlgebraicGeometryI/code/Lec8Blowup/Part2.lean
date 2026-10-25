/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec8Blowup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Projectivization.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.Lec8Blowup
open scoped LinearAlgebra.Projectivization


namespace Lec8Blowup

section EquationsEquiv

variable {k : Type*} [Field k] {n : ℕ}

/-- The fiber of the blowup projection over `0` is canonically the
projective space `ℙⁿ⁻¹` (exceptional divisor). -/
noncomputable def exceptionalFiberEquiv :
    {p : BlowupAffineOrigin k n // blowupProjection k n p = 0} ≃
    ℙ k (Fin n → k) where
  toFun p := p.1.1.2
  invFun l := ⟨⟨((0 : Fin n → k), l), zero_mem_blowupAffineOrigin l⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨⟨x, l⟩, hmem⟩, hproj⟩
    simp only [blowupProjection] at hproj
    subst hproj
    simp
  right_inv := by
    intro l
    simp

/-- Away from the origin, the blowup projection is a bijection between
the open locus of the blowup and the punctured affine space. -/
noncomputable def blowupAwayEquiv :
    {p : BlowupAffineOrigin k n // p.1.1 ≠ 0} ≃
    {x : Fin n → k // x ≠ 0} where
  toFun p := ⟨p.1.1.1, p.2⟩
  invFun x :=
    ⟨⟨(x.1, Projectivization.mk k x.1 x.2), by
      simp only [BlowupAffineOrigin, Set.mem_setOf_eq, Projectivization.submodule_mk]
      exact Submodule.mem_span_singleton_self x.1⟩, x.2⟩
  left_inv := by
    rintro ⟨⟨⟨x, l⟩, hmem⟩, hne⟩
    simp only [Subtype.mk.injEq]
    change x ≠ 0 at hne
    have hl : l = Projectivization.mk k x hne := proj_unique_of_nonzero hne l hmem
    ext <;> simp [hl]
  right_inv := by
    intro ⟨x, hx⟩
    simp

end EquationsEquiv
end Lec8Blowup
