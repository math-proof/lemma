/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.Basic.Part3
import Mathlib.Data.Fintype.BigOperators
import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsCone.Part2
set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup


namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- The **Perron–Frobenius property** for an indecomposable PSD off-diagonal-nonpositive form:
the kernel is 1-dimensional and spanned by a strictly positive vector $v > 0$. -/
class PerronFrobeniusProperty {B : Type*} [Fintype B] (f : B → B → ℝ) : Prop where
  kernel_span :
    CoxeterGroup.FormIndecomposable f →
    (∀ v : B → ℝ, ∑ s, ∑ t, v s * f s t * v t ≥ 0) →
    (∃ v : B → ℝ, v ≠ 0 ∧ ∑ s, ∑ t, v s * f s t * v t = 0) →
    (∀ s t, s ≠ t → f s t ≤ 0) →
    ∃ v : B → ℝ, (∀ s, v s > 0) ∧
      (∀ w : B → ℝ, (∑ s, ∑ t, w s * f s t * w t = 0) →
        ∃ c : ℝ, w = fun b => c * v b)

/-- Hypothesis class encoding the Coxeter classification theorem: a positive-definite Coxeter form
implies the underlying Coxeter group is **finite** (spherical type). Used as an axiom locally to
avoid invoking the full classification. -/
class SphericalFiniteProperty {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) : Prop where
  finite_of_pos_def :
    (∀ v : B → ℝ, v ≠ 0 → CoxeterGroup.bilinForm M v v > 0) → Finite (M.Group)

end CoxeterGroup
