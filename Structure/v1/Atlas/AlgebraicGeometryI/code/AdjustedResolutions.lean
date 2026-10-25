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
import Def.v1.Atlas.AlgebraicGeometryI.code.AdjustedResolutions


noncomputable section

open CategoryTheory Category Limits

universe v u

namespace AdjustedResolutions

/-- A *resolution* of an object `M` in an abelian category: a cochain complex `K•` together with a
quasi-isomorphism `M[0] → K•` from the complex concentrated in degree zero. -/
structure Resolution {C : Type u} [Category.{v} C] [Abelian C] (M : C) where
  cocomplex : CochainComplex C ℕ
  [hasHomology : ∀ i, cocomplex.HasHomology i]
  ι : (CochainComplex.single₀ C).obj M ⟶ cocomplex
  quasiIso : QuasiIso ι := by infer_instance

end AdjustedResolutions
end
