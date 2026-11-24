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
public import Structure.v1.Atlas.AlgebraicTopologyI.code.Section29
open DirectSum GradedMonoid


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section29.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace CupProduct

attribute [instance] GradedRAlgebra.instAddCommGroup GradedRAlgebra.instModule
  GradedRAlgebra.instGSemiring GradedRAlgebra.instGAlgebra

namespace GradedRAlgebra

variable {R : Type*} [CommRing R] (GA : GradedRAlgebra R)

/-- Multiplication in a graded $R$-algebra: $A_p \otimes A_q \to A_{p + q}$. -/
def mul {p q : ℤ} (x : GA.A p) (y : GA.A q) : GA.A (p + q) :=
  GMul.mul x y

/-- The unit map $\eta : R \to A_0$ of a graded $R$-algebra. -/
def unit : R →+ GA.A 0 :=
  GAlgebra.toFun

end GradedRAlgebra
end CupProduct
