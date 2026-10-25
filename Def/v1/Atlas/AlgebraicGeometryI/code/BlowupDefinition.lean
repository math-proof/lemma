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
open Polynomial AlgebraicGeometry


noncomputable section

namespace Blowup

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The `n`-th graded piece of the Rees algebra `R[It] = ⨁ Iⁿ tⁿ`: monomials `a · tⁿ` with
`a ∈ Iⁿ`, packaged as an additive subgroup of the Rees algebra. -/
def reesGrading (n : ℕ) : AddSubgroup (reesAlgebra I) where
  carrier := {f | ∃ a ∈ I ^ n, (f : R[X]) = Polynomial.monomial n a}
  add_mem' := by
    rintro ⟨fa, hfa⟩ ⟨fb, hfb⟩ ⟨a, ha, ha'⟩ ⟨b, hb, hb'⟩
    exact ⟨a + b, (I ^ n).add_mem ha hb, by
      show (⟨fa, hfa⟩ : reesAlgebra I).val + (⟨fb, hfb⟩ : reesAlgebra I).val = _
      rw [ha', hb']; simp [map_add]⟩
  zero_mem' := ⟨0, (I ^ n).zero_mem, by simp⟩
  neg_mem' := by
    rintro ⟨fv, hfv⟩ ⟨a, ha, ha'⟩
    exact ⟨-a, (I ^ n).neg_mem_iff.mpr ha, by
      show -(⟨fv, hfv⟩ : reesAlgebra I).val = _
      rw [ha']; simp [map_neg]⟩

end Blowup
end
