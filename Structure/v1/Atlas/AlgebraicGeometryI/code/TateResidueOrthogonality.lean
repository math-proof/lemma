/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateResidueOrthogonality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.TateCechInfra.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.TateCechInfra


noncomputable section

namespace TateResidueOrthogonality

open SerreDualityTate SerreDualityCurves

open CanonicalSheafCurves RiemannRochCurves SerreDualityP1

open SheafCohCurvesFiniteness CohomologyP1 SheafCohomology

open SerreDualityAnnihilator TateCechInfra


section SelfDuality

variable {k : Type*} [Field k]

/-- `Λ` is arithmetically discrete with respect to `W` iff `Λ / (W ∩ Λ)` is
finite-dimensional over `k`. -/
structure IsArithmeticallyDiscrete {V : Type*} [AddCommGroup V] [Module k V]
    (W Λ : Submodule k V) : Prop where
  finiteDim : Module.Finite k (Λ ⧸ Submodule.comap Λ.subtype (W ⊓ Λ))

/-- `Λ` is arithmetically cocompact with respect to `W` iff `V / (W + Λ)` is
finite-dimensional over `k`. -/
structure IsArithmeticallyCocompact {V : Type*} [AddCommGroup V] [Module k V]
    (W Λ : Submodule k V) : Prop where
  finiteDim : Module.Finite k (V ⧸ (W ⊔ Λ))

end SelfDuality
end TateResidueOrthogonality
end
