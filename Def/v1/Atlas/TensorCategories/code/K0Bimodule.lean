/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.GrothendieckRing.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRing
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Group.Opposite
import Instance.v1.Atlas.TensorCategories.code.K0Bimodule.Part2
set_option maxHeartbeats 800000

open Finset FusionRing


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

/-- Left action of the Grothendieck ring of `R` on `K₀(R)` in coefficient form, defined by
`(r ◃ p)_k = Σᵢⱼ rᵢ pⱼ N_{i* k j}`. -/
def k0ActLeft (r p : ι → ℤ) : ι → ℤ :=
  fun k => univ.sum fun i => univ.sum fun j => r i * p j * (R.N (R.star i) k j : ℤ)

/-- Right action of the Grothendieck ring of `R` on `K₀(R)` in coefficient form, defined by
`(p ▹ r)_k = Σ_{a,j} pₐ rⱼ N_{k j* a}`. -/
def k0ActRight (p r : ι → ℤ) : ι → ℤ :=
  fun k => univ.sum fun a => univ.sum fun j => p a * r j * (R.N k (R.star j) a : ℤ)

/-- The involutive duality on the index set viewed as a self-equivalence of `ι`. -/
noncomputable def starEquiv : ι ≃ ι where
  toFun := R.star
  invFun := R.star
  left_inv := R.star_star
  right_inv := R.star_star

end FusionRing
