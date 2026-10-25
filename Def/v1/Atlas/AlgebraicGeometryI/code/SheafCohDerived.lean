/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohDerived.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.EffaceableUniversal
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.EffaceableUniversal
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SheafCohomology
import Theorem.v1.Atlas.AlgebraicGeometryI.code.SheafCohomology.Part2
import Structure.v1.Atlas.AlgebraicGeometryI.code.SheafCohDerived


noncomputable section

open CohomologyP1 SheafCohomology CategoryTheory CategoryTheory.Limits

namespace SheafCohDerived

section CechDeltaFunctorData

variable (k : Type) [Field k]

/-- Construct the Čech `δ`-functor on `ℙ¹` from the explicit sheaf cohomology
groups `H⁰`, `H¹`. -/
def mkCechDeltaFunctorP1 : CechDeltaFunctorP1 k where
  dimH0 := fun n => Module.finrank k (H0 k n)
  dimH1 := fun n => Module.finrank k (H1 k n)
  dimH0_nonneg := fun n hn => finrank_H0_of_nonneg k n hn
  dimH0_neg := fun n hn => finrank_H0_of_neg k n hn
  dimH1_nonneg := fun n hn => finrank_H1_of_nonneg k n hn
  dimH1_neg := fun n hn => finrank_H1_of_neg k n hn
  euler := fun n => euler_characteristic k n

end CechDeltaFunctorData
end SheafCohDerived
end
