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
public import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section29.Part3
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

/-- Identification of the Mathlib sphere `TopCat.sphere m` with the
`SphereHomology.Sphere m` used elsewhere in Atlas, via the canonical `ULift`
homeomorphism. -/
noncomputable def sphereTopCatIso (m : ℕ) :
    TopCat.sphere.{0} m ≅ TopCat.of (SphereHomology.Sphere m) :=
  TopCat.isoOfHomeo Homeomorph.ulift

/-- Identification of the Mathlib sphere `TopCat.sphere m` with the local
`SphereHomology.Sphere m`, repeated here in the `SphereHomology` namespace for
ergonomic access. -/
noncomputable def sphereTopCatIso (m : ℕ) :
    TopCat.sphere.{0} m ≅ TopCat.of (SphereHomology.Sphere m) :=
  TopCat.isoOfHomeo Homeomorph.ulift

/-- Functoriality of the singular chain complex with $\mathbb{Z}$-coefficients:
a homeomorphism (or `TopCat`-iso) $X \simeq Y$ induces an isomorphism of chain
complexes $C_*(X; \mathbb{Z}) \simeq C_*(Y; \mathbb{Z})$. -/
noncomputable def singularChainComplexZ_iso_of_topIso {X Y : TopCat.{0}} (e : X ≅ Y) :
    singularChainComplexZ X ≅ singularChainComplexZ Y :=
  ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).mapIso e

end SphereCupProduct
end CupProduct
end
