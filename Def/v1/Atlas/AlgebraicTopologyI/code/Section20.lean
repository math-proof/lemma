/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section20.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.RingTheory.Flat.Basic
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
public import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section20

@[expose] public section

namespace TensorProduct

open TensorProduct

variable {R : Type*} [CommSemiring R]

variable {M N P : Type*}

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]

variable [Module R M] [Module R N] [Module R P]

/-- (Definition 20.3) The universal property of the tensor product as the universal $R$-bilinear
target: $R$-bilinear maps $M \times N \to P$ are in linear bijection with $R$-linear maps
$M \otimes_R N \to P$. -/
def universalProperty :
    (M →ₗ[R] N →ₗ[R] P) ≃ₗ[R] (M ⊗[R] N →ₗ[R] P) :=
  TensorProduct.lift.equiv (RingHom.id R) M N P

end TensorProduct
