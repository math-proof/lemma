/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjustedResolutions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Preserves.Finite


noncomputable section

open CategoryTheory Category Limits

universe v u

namespace AdjustedResolutions

/-- An object `M` is *adjusted to* an additive functor `F` if all higher right derived functors
of `F` vanish on `M`: `RⁱF(M) = 0` for `i > 0`. Such objects (e.g. injectives, or `F`-acyclic
objects) can be used in place of injective resolutions when computing `RF`. -/
def IsAdjustedToFunctor
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (M : C) : Prop :=
  ∀ (i : ℕ), 0 < i → IsZero ((F.rightDerived i).obj M)

end AdjustedResolutions
end
