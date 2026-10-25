/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section20.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.RingTheory.Flat.Basic
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section20


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
