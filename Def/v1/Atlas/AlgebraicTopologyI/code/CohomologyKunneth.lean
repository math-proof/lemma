module
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section33.Part2
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section33
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section29
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section25
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section29.Part7
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section25.Part3
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Basis.Prod
public import Abbrev.v1.Atlas.AlgebraicTopologyI.code.CohomologyKunneth
open CategoryTheory AlgebraicTopology Limits SingularCohomology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/CohomologyKunneth.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open scoped TensorProduct

namespace CohomologyKunneth

/-- The bidegree-`(p, q)` component of the cohomology cross product, viewed as
a linear map from `H^p(X; R) ⊗ H^q(Y; R)` into the total cohomology
`⨁_n H^n(X × Y; R)` by landing in the degree `p + q` summand. -/
def componentCrossMap
    (R : Type) [CommRing R] (X Y : TopCat.{0}) (pq : ℕ × ℕ) :
    TensorProduct R (singularCohomologyFamily R X pq.1)
      (singularCohomologyFamily R Y pq.2) →ₗ[R]
      totalSingularCohomology R (TopCat.of (↑X × ↑Y)) :=
  (DirectSum.lof R ℕ (singularCohomologyFamily R (TopCat.of (↑X × ↑Y))) (pq.1 + pq.2)).comp
    (cohomologyCross R X Y pq.1 pq.2)

/-- The total cohomology cross product
`× : H^*(X; R) ⊗_R H^*(Y; R) → H^*(X × Y; R)`, built by distributing the tensor
product over the direct-sum decompositions and assembling the bidegree
components `componentCrossMap`. -/
def totalCohomologyCrossProduct
    (R : Type) [CommRing R] (X Y : TopCat.{0}) :
    (totalSingularCohomology R X ⊗[R]
      totalSingularCohomology R Y) →ₗ[R]
      totalSingularCohomology R (TopCat.of (↑X × ↑Y)) :=
  (DirectSum.toModule R (ℕ × ℕ)
    (totalSingularCohomology R (TopCat.of (↑X × ↑Y)))
    (componentCrossMap R X Y)).comp
    (TensorProduct.directSum R R
      (singularCohomologyFamily R X)
      (singularCohomologyFamily R Y)).toLinearMap

end CohomologyKunneth
end
