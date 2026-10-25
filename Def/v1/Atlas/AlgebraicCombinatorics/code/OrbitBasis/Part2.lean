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
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.OrbitBasis
set_option autoImplicit false


noncomputable section

open scoped Classical

open Finset Finsupp MulAction Function Module

namespace OrbitBasis

variable (G : Type*) [Group G] (α : Type*) [Fintype α] [DecidableEq α] [MulAction G α]

attribute [local instance] Finsupp.comapSMul Finsupp.comapMulAction
  Finsupp.comapDistribMulAction

def invariantSubspace : Submodule ℝ (α →₀ ℝ) where
  carrier := {v | ∀ g : G, g • v = v}
  add_mem' {a b} ha hb g := by
    have := ha g; have := hb g
    ext x; simp only [Finsupp.add_apply, Finsupp.comapSMul_apply]
    rw [← DFunLike.congr_fun (ha g) x, ← DFunLike.congr_fun (hb g) x]
    simp [Finsupp.comapSMul_apply]
  zero_mem' g := by ext x; simp

  smul_mem' r {v} hv g := by
    ext a
    change (g • (r • v)) a = (r • v) a
    rw [Finsupp.comapSMul_apply]
    have h4 := DFunLike.congr_fun (hv g) a
    rw [Finsupp.comapSMul_apply] at h4
    simp only [Finsupp.smul_apply, smul_eq_mul, h4]

end OrbitBasis
end
