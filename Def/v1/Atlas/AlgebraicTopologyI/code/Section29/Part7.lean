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
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section29.Part3
open DirectSum GradedMonoid

open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI


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
