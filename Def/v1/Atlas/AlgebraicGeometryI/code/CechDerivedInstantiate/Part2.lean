/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechDerivedInstantiate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.AlgebraicGeometryI.code.CohomologyConnection
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CohomologyConnection
import Structure.v1.Atlas.AlgebraicGeometryI.code.CechDerivedInstantiate


noncomputable section

open CategoryTheory CategoryTheory.Limits

open SheafCohomology CohomologyP1 DerivedFunctorsDefs


namespace DerivedFunctorsDefs

universe v₀ u₀

variable {C : Type u₀} [Category.{v₀} C] [Abelian C]
         {D : Type*} [Category D] [Abelian D]

variable (k : Type) [Field k]

/-- Concrete construction of the `CechToDerivedDataP1Witness` for `P¹` over `k`, drawing on the
`SheafCohomology` and `SheafCohDerived` lemmas. -/
def mkCechToDerivedDataP1Witness : CechToDerivedDataP1Witness k where
  h1_vanishing := SheafCohomology.finrank_H1_of_nonneg k
  euler_char := SheafCohomology.euler_characteristic k
  effaceability := SheafCohDerived.cech_effaceability_witness k
  serre_duality := SheafCohDerived.serre_duality_derived k

end DerivedFunctorsDefs
end
