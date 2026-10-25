/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupDefinition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.GradedAlgebra.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.BlowupDefinition
open Polynomial AlgebraicGeometry


noncomputable section

namespace Blowup

variable {R : Type*} [CommRing R] (I : Ideal R)

set_option synthInstance.maxHeartbeats 400000 in
/-- Each graded piece `reesGrading I n` carries the inherited `AddCommMonoid` structure. -/
instance reesGrading_addCommMonoid (n : ℕ) : AddCommMonoid ↥(reesGrading I n) := inferInstance

end Blowup
end
