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
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11

namespace BilinearMap

/-- (Definition 20.1) The type of $R$-bilinear maps $\beta : M \times N \to P$, encoded as a
linear map $M \to (N \to_{R} P)$; concretely $\beta$ satisfies
$\beta(x+x', y) = \beta(x,y) + \beta(x',y)$, $\beta(x, y+y') = \beta(x,y) + \beta(x,y')$,
$\beta(rx,y) = r\beta(x,y)$, $\beta(x,ry) = r\beta(x,y)$. -/
abbrev BilinearMapType (R : Type*) [CommSemiring R]
    (M N P : Type*) [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P] :=
  M →ₗ[R] N →ₗ[R] P

end BilinearMap

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
