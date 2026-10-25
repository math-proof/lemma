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
