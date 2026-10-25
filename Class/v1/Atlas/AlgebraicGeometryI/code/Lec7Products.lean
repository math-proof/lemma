/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7Products.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Instance.v1.Atlas.AlgebraicGeometryI.code.Lec7Products
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct


namespace Lec7Products

section Goal62

/-- A scheme `X` is projective if it admits a closed immersion into
some `Proj 𝒜` of a graded ring (Lec 7, Prop 8 setting). -/
class Scheme.IsProjective (X : Scheme) : Prop where
  exists_closedImmersion_into_proj :
    ∃ (A : Type) (σ : Type) (_ : CommRing A) (_ : SetLike σ A)
      (_ : AddSubgroupClass σ A) (𝒜 : ℕ → σ) (_ : GradedRing 𝒜)
      (f : X ⟶ Proj 𝒜), IsClosedImmersion f

end Goal62
end Lec7Products
