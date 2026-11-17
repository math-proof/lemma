/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7Products.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Class.v1.Atlas.AlgebraicGeometryI.code.Lec7Products

@[expose] public section

set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct


namespace Lec7Products

section Goal62

/-- `Proj 𝒜` is projective via the identity closed immersion. -/
noncomputable instance proj_isProjective
    {A : Type} {σ : Type} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] :
    Scheme.IsProjective (Proj 𝒜) where
  exists_closedImmersion_into_proj :=
    ⟨A, σ, inferInstance, inferInstance, inferInstance, 𝒜, inferInstance,
     𝟙 (Proj 𝒜), inferInstance⟩

end Goal62
end Lec7Products
