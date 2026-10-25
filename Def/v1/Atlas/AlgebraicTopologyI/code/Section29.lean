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
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section29
open DirectSum GradedMonoid


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
