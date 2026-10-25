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
import Def.v1.Atlas.AlgebraicGeometryI.code.Prop34BlowupProperties
open Polynomial AlgebraicGeometry


noncomputable section

namespace Prop34Blowup

variable {R : Type*} [CommRing R]

/-- The commutative ring structure on the associated graded ring. -/
noncomputable instance assocGradedRing.commRing (𝔪 : Ideal R) :
    CommRing (assocGradedRing 𝔪) :=
  Ideal.Quotient.commRing (reesIdealFromBase 𝔪)

end Prop34Blowup
end
