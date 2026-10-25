/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec8Blowup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Projectivization.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec8Blowup
open scoped LinearAlgebra.Projectivization


namespace Lec8Blowup

section EquationsEquiv

variable {k : Type*} [Field k] {n : ℕ}

/-- A point of projective space is the span of its chosen
representative. -/
lemma Projectivization.submodule_eq_span_rep (v : ℙ k (Fin n → k)) :
    v.submodule = k ∙ v.rep := by
  conv_lhs => rw [← Projectivization.mk_rep v]
  exact Projectivization.submodule_mk _ _

/-- A nonzero vector `x` determines the unique line in `ℙⁿ⁻¹`
containing it. -/
lemma proj_unique_of_nonzero {x : Fin n → k} (hx : x ≠ 0)
    (l : ℙ k (Fin n → k)) (hmem : x ∈ l.submodule) :
    l = Projectivization.mk k x hx := by
  rw [Projectivization.submodule_eq_span_rep, Submodule.mem_span_singleton] at hmem
  obtain ⟨a, ha⟩ := hmem
  have ha_ne : a ≠ 0 := by intro h; simp [h] at ha; exact hx ha.symm
  rw [← Projectivization.mk_rep l, Projectivization.mk_eq_mk_iff]
  exact ⟨Units.mk0 a⁻¹ (inv_ne_zero ha_ne), by
    simp only [Units.smul_def, Units.val_mk0]
    rw [← ha, smul_smul, inv_mul_cancel₀ ha_ne, one_smul]⟩

/-- For any line `ℓ`, the point `(0, ℓ)` lies on the blowup (the
exceptional fiber). -/
lemma zero_mem_blowupAffineOrigin (l : ℙ k (Fin n → k)) :
    ((0 : Fin n → k), l) ∈ BlowupAffineOrigin k n := by
  simp only [BlowupAffineOrigin, Set.mem_setOf_eq,
    Projectivization.submodule_eq_span_rep, Submodule.mem_span_singleton]
  exact ⟨0, by simp⟩

end EquationsEquiv
end Lec8Blowup
