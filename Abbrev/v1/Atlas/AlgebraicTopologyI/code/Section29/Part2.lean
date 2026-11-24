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
public import Structure.v1.Atlas.AlgebraicTopologyI.code.Section29.Part3
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

namespace CupProduct

section SphereCupProduct

open CategoryTheory AlgebraicTopology Limits

variable (R : Type) [CommRing R]

/-- The singular cochain complex $C^*(X; G) = \mathrm{Hom}_R(C_*(X; R), G)$ of a
topological space $X$ with coefficients in an $R$-module $G$, as an object of
`CochainComplex (ModuleCat R) ℕ`. -/
noncomputable abbrev singCochains (G : ModuleCat.{0} R) (X : TopCat.{0}) :
    CochainComplex (ModuleCat R) ℕ :=
  (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
    (ModuleCat.of R R)).obj X).linearYonedaObj R G

/-- The $n$-th singular cohomology $H^n(X; G)$ as an $R$-module, defined as the
homology of the cochain complex `singCochains R G X` in degree $n$. -/
noncomputable abbrev singCohom (G : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    ModuleCat R :=
  (singCochains R G X).homology n

end SphereCupProduct
end CupProduct
end
