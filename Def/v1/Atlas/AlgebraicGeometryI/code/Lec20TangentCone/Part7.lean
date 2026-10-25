/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20TangentCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.AlgebraicGeometry.Scheme
import Instance.v1.Atlas.AlgebraicGeometryI.code.Lec20TangentCone.Part2
open Polynomial


namespace Lec20TangentCone

universe u

variable {R : Type u} [CommRing R]

/-- Algebra isomorphism realising the associated graded ring as the exceptional fiber
of the blow-up: `gr_𝔪(R) ≃ reesAlgebra 𝔪 ⊗_R (R⧸𝔪)`. -/
noncomputable def assocGradedRing_equivExceptionalFiber (𝔪 : Ideal R) :
    assocGradedRing 𝔪 ≃ₐ[↥(reesAlgebra 𝔪)] TensorProduct R (↥(reesAlgebra 𝔪)) (R ⧸ 𝔪) := by
  unfold assocGradedRing
  exact Algebra.TensorProduct.quotIdealMapEquivTensorQuot (↥(reesAlgebra 𝔪)) 𝔪

/-- The ring isomorphism underlying the algebra equivalence
`gr_𝔪(R) ≃ reesAlgebra 𝔪 ⊗_R (R⧸𝔪)`. -/
noncomputable def assocGradedRing_ringEquivExceptionalFiber (𝔪 : Ideal R) :
    assocGradedRing 𝔪 ≃+* TensorProduct R (↥(reesAlgebra 𝔪)) (R ⧸ 𝔪) :=
  (assocGradedRing_equivExceptionalFiber 𝔪).toRingEquiv

/-- The exceptional fiber of the blow-up `Bl_𝔪(Spec R) → Spec R` above the closed point,
realised as `Spec(reesAlgebra 𝔪 ⊗_R (R⧸𝔪))`. -/
noncomputable def exceptionalFiberScheme (𝔪 : Ideal R) : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (.of (TensorProduct R (↥(reesAlgebra 𝔪)) (R ⧸ 𝔪)))

/-- Scheme-theoretic isomorphism identifying the tangent cone with the exceptional fiber
of the blow-up. -/
noncomputable def tangentCone_isoExceptionalFiber (𝔪 : Ideal R) :
    tangentCone 𝔪 ≅ exceptionalFiberScheme 𝔪 := by
  unfold tangentCone exceptionalFiberScheme
  exact AlgebraicGeometry.Scheme.Spec.mapIso
    (assocGradedRing_ringEquivExceptionalFiber 𝔪).symm.toCommRingCatIso.op

/-- The `n`-th graded piece `𝔪^n / 𝔪^{n+1}` of the associated graded ring `gr_𝔪(R)`. -/
def assocGradedPiece (𝔪 : Ideal R) (n : ℕ) : Type _ :=
  ↥(𝔪 ^ n) ⧸ (𝔪 • ⊤ : Submodule R ↥(𝔪 ^ n))

end Lec20TangentCone
