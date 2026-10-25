/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/FundamentalThm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Projective.Resolution


noncomputable section

open CategoryTheory Category Limits ChainComplex HomologicalComplex

universe v u

namespace FundamentalThm

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A resolution of an object `Z` in an abelian category: a chain complex equipped with a
quasi-isomorphism to the chain complex concentrated in degree zero on `Z`. -/
structure Resolution (Z : C) where
  complex : ChainComplex C ℕ
  [hasHomology : ∀ (i : ℕ), complex.HasHomology i]
  π : complex ⟶ (ChainComplex.single₀ C).obj Z
  [quasiIso : QuasiIso π]

end FundamentalThm
end
