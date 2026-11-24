module
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part24
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section10
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section27
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
public import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section27
public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Topology.Category.TopCat.Sphere
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.LinearAlgebra.DirectSum.Basis
public import Instance.v1.Atlas.AlgebraicTopologyI.code.Section29
open DirectSum GradedMonoid
open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section29.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace SingularCohomology

variable (R : Type) [CommRing R]

/-- The cup product on singular cohomology, as a graded multiplication
$\smile : H^p(X) \otimes H^q(X) \to H^{p + q}(X)$. -/
def cupMul (X : TopCat.{0}) {p q : ℕ}
    (x : singularCohomologyFamily R X p) (y : singularCohomologyFamily R X q) :
    singularCohomologyFamily R X (p + q) :=
  (cupProduct R X p q).hom (x ⊗ₜ[R] y)


end SingularCohomology
end
