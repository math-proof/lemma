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
import Def.v1.Atlas.AlgebraicGeometryI.code.Prop34BlowupProperties.Part2
open Polynomial AlgebraicGeometry


noncomputable section

namespace Prop34Blowup

variable {R : Type*} [CommRing R]

/-- Scaling preserves membership in the Rees algebra. -/
lemma scaleAlgHom_mem_reesAlgebra (I : Ideal R) (c : R)
    (f : R[X]) (hf : f ∈ reesAlgebra I) :
    (scaleAlgHom c : R[X] →ₐ[R] R[X]) f ∈ reesAlgebra I := by
  have h : (reesAlgebra I).map (scaleAlgHom c) ≤ reesAlgebra I := by
    rw [← adjoin_monomial_eq_reesAlgebra, ← Algebra.adjoin_image R (scaleAlgHom c)]
    apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simp only [SetLike.mem_coe, Submodule.mem_map] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    rw [adjoin_monomial_eq_reesAlgebra, SetLike.mem_coe]
    unfold scaleAlgHom
    simp only [aeval_def, eval₂_monomial, Polynomial.algebraMap_eq, pow_one]
    rw [← mul_assoc, ← map_mul, C_mul_X_eq_monomial, reesAlgebra.monomial_mem, pow_one]
    exact I.mul_mem_right c hr
  exact h ⟨f, hf, rfl⟩

end Prop34Blowup
end
