/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.v1.Atlas.AlgebraicGeometryI.code.KrullDimensionAffineSpace
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.KrullDimensionAffineSpace
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.FiniteMorphismDimension
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Finite

@[expose] public section

set_option maxHeartbeats 800000


noncomputable section

open MvPolynomial

set_option backward.isDefEq.respectTransparency false

/-- The standard algebra isomorphism
`k[x₁,…,xₙ] ⊗_k k[y₁,…,yₘ] ≃ k[x₁,…,xₙ, y₁,…,yₘ]`. -/
def mvPolynomialTensorAlgEquiv (k : Type*) [CommRing k]
    (n m : ℕ) :
    TensorProduct k (MvPolynomial (Fin n) k) (MvPolynomial (Fin m) k) ≃ₐ[k]
      MvPolynomial (Fin (n + m)) k :=
  (tensorEquivSum k (Fin n) (Fin m) k).trans
    (renameEquiv k finSumFinEquiv)

end
