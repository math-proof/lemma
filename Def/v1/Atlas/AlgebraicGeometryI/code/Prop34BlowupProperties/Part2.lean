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
import Instance.v1.Atlas.AlgebraicGeometryI.code.Prop34BlowupProperties.Part2
open Polynomial AlgebraicGeometry


noncomputable section

namespace Prop34Blowup

variable {R : Type*} [CommRing R]

/-- Algebra isomorphism between the associated graded ring and the exceptional fibre
ring, viewed over the Rees algebra. -/
noncomputable def assocGraded_equivExceptionalFiber (𝔪 : Ideal R) :
    assocGradedRing 𝔪 ≃ₐ[↥(reesAlgebra 𝔪)] exceptionalFiberRing 𝔪 := by
  unfold assocGradedRing
  exact Algebra.TensorProduct.quotIdealMapEquivTensorQuot (↥(reesAlgebra 𝔪)) 𝔪

/-- Ring isomorphism `gr_𝔪 R ≅ reesAlgebra 𝔪 ⊗_R R/𝔪`. -/
noncomputable def assocGraded_ringEquivExceptionalFiber (𝔪 : Ideal R) :
    assocGradedRing 𝔪 ≃+* exceptionalFiberRing 𝔪 :=
  (assocGraded_equivExceptionalFiber 𝔪).toRingEquiv

/-- The tangent cone scheme: `Spec (gr_𝔪 R)`. -/
noncomputable def tangentConeScheme (𝔪 : Ideal R) : Scheme :=
  Spec (.of (assocGradedRing 𝔪))

/-- The exceptional fibre of the blowup as a scheme. -/
noncomputable def exceptionalFiberScheme (𝔪 : Ideal R) : Scheme :=
  Spec (.of (exceptionalFiberRing 𝔪))

/-- Proposition 34 (key isomorphism): the tangent cone scheme is canonically isomorphic
to the exceptional fibre of the blowup. -/
noncomputable def tangentCone_isoExceptionalFiber (𝔪 : Ideal R) :
    tangentConeScheme 𝔪 ≅ exceptionalFiberScheme 𝔪 := by
  unfold tangentConeScheme exceptionalFiberScheme
  exact Scheme.Spec.mapIso
    (assocGraded_ringEquivExceptionalFiber 𝔪).symm.toCommRingCatIso.op

/-- The `R`-algebra endomorphism of `R[X]` sending `X ↦ c · X`, used to define the
scaling action on the Rees algebra. -/
noncomputable def scaleAlgHom (c : R) : R[X] →ₐ[R] R[X] :=
  aeval (C c * X)

end Prop34Blowup
end
