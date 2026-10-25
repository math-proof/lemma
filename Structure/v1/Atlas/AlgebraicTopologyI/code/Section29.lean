/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section29.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part24
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section10
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section27
import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section27
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Algebra.Algebra.TransferInstance
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.DirectSum.Basis
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
