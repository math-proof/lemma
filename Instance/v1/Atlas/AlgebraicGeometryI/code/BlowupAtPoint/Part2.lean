/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupAtPoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.GradedAlgebra.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.BlowupAtPoint
open Polynomial AlgebraicGeometry


noncomputable section

namespace BlowupAtPoint

variable {R : Type*} [CommRing R] (I : Ideal R)

set_option synthInstance.maxHeartbeats 400000 in
/-- The Rees algebra together with `reesGrading` is a graded ring. -/
instance reesGradedRing : GradedRing (reesGrading I) :=
  { (reesGrading_isInternal I).chooseDecomposition with
    one_mem := reesGrading_one_mem I
    mul_mem := fun {_i} {_j} {_fi} {_fj} hi hj => reesGrading_mul_mem I hi hj }

end BlowupAtPoint
end
