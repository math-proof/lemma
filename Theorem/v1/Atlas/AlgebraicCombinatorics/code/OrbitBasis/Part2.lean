/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/OrbitBasis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Def.v1.Atlas.AlgebraicCombinatorics.code.OrbitBasis.Part2
set_option autoImplicit false


noncomputable section

open scoped Classical

open Finset Finsupp MulAction Function Module

namespace OrbitBasis

variable (G : Type*) [Group G] (α : Type*) [Fintype α] [DecidableEq α] [MulAction G α]

attribute [local instance] Finsupp.comapSMul Finsupp.comapMulAction
  Finsupp.comapDistribMulAction

variable {G α}

theorem invariant_iff_constant_on_orbits {v : α →₀ ℝ} :
    v ∈ invariantSubspace G α ↔
      ∀ a b : α, (Quotient.mk'' a : orbitRel.Quotient G α) = Quotient.mk'' b →
        v a = v b := by
  constructor
  · intro hv a b hab
    have hmem := Quotient.eq''.mp hab
    rw [orbitRel_apply] at hmem
    obtain ⟨g, hg⟩ := hmem
    have h1 := DFunLike.congr_fun (hv g) a
    rw [Finsupp.comapSMul_apply] at h1
    rw [← h1, ← hg, inv_smul_smul]
  · intro hconst g
    ext a
    rw [Finsupp.comapSMul_apply]
    exact (hconst _ _ (Quotient.eq''.mpr (orbitRel_apply.mpr ⟨g, smul_inv_smul g a⟩))).symm

end OrbitBasis
end
