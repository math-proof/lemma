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
public import Instance.v1.Atlas.AlgebraicTopologyI.code.Section29.Part3
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

/-- The natural-number cast $\mathbb{N} \to H^0(X; R)$, defined recursively as
$n \mapsto n \cdot 1_{H^*(X; R)}$. Provides the `natCast` field for the graded
ring structure on $H^*(X; R)$. -/
def cupProduct_natCast
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    ℕ → singularCohomologyFamily R X 0
  | 0 => 0
  | n + 1 => cupProduct_natCast R X n + GradedMonoid.GOne.one


/-- The integer cast $\mathbb{Z} \to H^0(X; R)$, extending the natural-number cast
by negation on negative integers. Provides the `intCast` field for the graded
ring structure. -/
def cupProduct_intCast
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    ℤ → singularCohomologyFamily R X 0
  | Int.ofNat n => cupProduct_natCast R X n
  | Int.negSucc n => -cupProduct_natCast R X (n + 1)

/-- Graded ring structure on the cohomology family $n \mapsto H^n(X; R)$,
assembling unit, associativity, distributivity and the natural/integer casts
proved above. This is what promotes $H^*(X; R) = \bigoplus_n H^n(X; R)$ to a ring
under cup product. -/
def cohomologyAlgebraMap
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    R →+ singularCohomologyFamily R X 0 where
  toFun r := r • cohomologyUnit R X
  map_zero' := by simp [zero_smul]
  map_add' r s := by simp [add_smul]

/-- Compatibility of $R$-scalar multiplication with the algebra map:
$r \cdot x = \eta(r) \smile x$. Together with the previous lemmas this gives the
$R$-algebra structure on $H^*(X; R)$. -/
def CupProductAlgebra.equiv (X : TopCat.{0}) :
    CupProductAlgebra R X ≃
      DirectSum ℕ (singularCohomologyFamily R X) where
  toFun a := a.toDirectSum
  invFun d := ⟨d⟩
  left_inv _ := rfl
  right_inv _ := rfl


/-- The ring structure on $H^*(X; R) = \bigoplus_n H^n(X; R)$, transferred from
the direct sum along `CupProductAlgebra.equiv`. -/
@[reducible]
noncomputable def instRingCupProductAlgebra
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    Ring (CupProductAlgebra R X) :=
  (CupProductAlgebra.equiv R X).ring

attribute [instance] instRingCupProductAlgebra


/-- The $R$-algebra structure on the cohomology ring $H^*(X; R)$, also transferred
from the direct sum along `CupProductAlgebra.equiv`. -/
@[reducible]
noncomputable def instAlgebraCupProductAlgebra
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    @Algebra R (CupProductAlgebra R X) _
      (instRingCupProductAlgebra R X).toSemiring :=
  (CupProductAlgebra.equiv R X).algebra R

end SingularCohomology
end
