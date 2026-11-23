/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section29.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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
public section

open DirectSum GradedMonoid


namespace CupProduct

/-- **Definition 29.1.** A *graded $R$-algebra* (for $R$ a commutative ring) is
a $\mathbb{Z}$-graded $R$-module $A_*$ equipped with multiplication maps
$A_p \otimes_R A_q \to A_{p+q}$ and a unit $\eta : R \to A_0$ satisfying the
usual associativity and unit diagrams.

This bundles a family of $R$-modules with the graded-semiring/graded-algebra
data taken from Mathlib's `DirectSum` / `GAlgebra` API. -/
structure GradedRAlgebra (R : Type*) [CommRing R] where
  A : ℤ → Type*
  instAddCommGroup : ∀ i, AddCommGroup (A i)
  instModule : ∀ i, Module R (A i)
  instGSemiring : GSemiring A
  instGAlgebra : GAlgebra R A

end CupProduct
