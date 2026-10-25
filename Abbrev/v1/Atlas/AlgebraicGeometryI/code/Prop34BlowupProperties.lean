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
import Instance.v1.Atlas.AlgebraicGeometryI.code.Prop34BlowupProperties
open Polynomial AlgebraicGeometry


noncomputable section

namespace Prop34Blowup

variable {R : Type*} [CommRing R]

/-- The fibre of the blowup over the centre, realised as the tensor product
`reesAlgebra 𝔪 ⊗_R R/𝔪`. -/
abbrev exceptionalFiberRing (𝔪 : Ideal R) :=
  TensorProduct R (↥(reesAlgebra 𝔪)) (R ⧸ 𝔪)

end Prop34Blowup
end
