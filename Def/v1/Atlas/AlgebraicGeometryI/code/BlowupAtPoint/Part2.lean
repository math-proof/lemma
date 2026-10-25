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
import Instance.v1.Atlas.AlgebraicGeometryI.code.BlowupAtPoint
open Polynomial AlgebraicGeometry


noncomputable section

namespace BlowupAtPoint

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The component of `f ∈ R[It]` in the `n`-th graded piece, namely the monomial
`f.coeff n · tⁿ`. -/
def reesDecomposeComponent (f : reesAlgebra I) (n : ℕ) :
    ↥(reesGrading I n) := by
  refine ⟨⟨monomial n (f.val.coeff n), ?_⟩, ?_⟩
  · exact reesAlgebra.monomial_mem.mpr (((mem_reesAlgebra_iff I f.val).mp f.property) n)
  · exact ⟨f.val.coeff n, ((mem_reesAlgebra_iff I f.val).mp f.property) n, rfl⟩

end BlowupAtPoint
end
