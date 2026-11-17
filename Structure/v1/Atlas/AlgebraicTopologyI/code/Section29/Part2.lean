/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section29.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part24
public import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section10
public import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
public import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section27
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
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section29
open DirectSum GradedMonoid


namespace CupProduct

attribute [instance] GradedRAlgebra.instAddCommGroup GradedRAlgebra.instModule
  GradedRAlgebra.instGSemiring GradedRAlgebra.instGAlgebra

namespace GradedRAlgebra

variable {R : Type*} [CommRing R] (GA : GradedRAlgebra R)

/-- A graded $R$-algebra $A$ is *(graded) commutative* if the twist isomorphism
satisfies $\tau(x \otimes y) = (-1)^{pq} y \otimes x$, i.e.
$$x \cdot y = (-1)^{pq} y \cdot x$$
for $x \in A_p$ and $y \in A_q$. This is the Koszul sign rule, as used for
example in singular cohomology under cup product. -/
structure IsGradedCommutative : Prop where
  mul_comm : ∀ (p q : ℤ) (x : GA.A p) (y : GA.A q),
    GMul.mul x y =
      ((p * q).negOnePow : ℤ) • cast (congrArg GA.A (add_comm q p)) (GMul.mul y x)

end GradedRAlgebra

end CupProduct

open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI

public noncomputable section

namespace SingularCohomology

variable (R : Type) [CommRing R]

/-- The total cohomology ring $H^*(X; R) = \bigoplus_{n \ge 0} H^n(X; R)$ of a
space $X$ with coefficients in $R$, as a wrapper around the direct sum of
singular cohomology groups. It will be given the structure of a graded
$R$-algebra via the cup product. -/
structure CupProductAlgebra (X : TopCat.{0}) : Type where
  toDirectSum : DirectSum ℕ (fun n ↦
    (singularCohomology R X (ModuleCat.of R R) n : Type))

end SingularCohomology
end
