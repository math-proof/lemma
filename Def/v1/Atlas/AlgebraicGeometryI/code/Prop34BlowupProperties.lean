/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop34BlowupProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Nilpotent.Lemmas
import Def.v1.Atlas.AlgebraicGeometryI.code.BlowupAtPoint.Part3
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.BlowupAtPoint
open Polynomial AlgebraicGeometry


noncomputable section

namespace Prop34Blowup

variable {R : Type*} [CommRing R]

/-- The image of an ideal `𝔪 ⊆ R` inside the Rees algebra `R[𝔪 t]`. -/
noncomputable def reesIdealFromBase (𝔪 : Ideal R) : Ideal (reesAlgebra 𝔪) :=
  Ideal.map (algebraMap R (reesAlgebra 𝔪)) 𝔪

/-- The associated graded ring `gr_𝔪 R = ⨁ 𝔪^n / 𝔪^{n+1}`, defined as the Rees algebra
quotiented by the image of `𝔪`. -/
def assocGradedRing (𝔪 : Ideal R) : Type _ :=
  (reesAlgebra 𝔪) ⧸ reesIdealFromBase 𝔪

end Prop34Blowup
end
