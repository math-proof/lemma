/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CurveTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ArithmeticGeometry.code.MorphismsCurves
import Abbrev.v1.Atlas.ArithmeticGeometry.code.RegularLocalRings
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.RegularLocalRings
import Def.v1.Atlas.ArithmeticGeometry.code.CurveTheory.Part9


noncomputable section

open Module IsDiscreteValuationRing

namespace ArithmeticGeometry

section DVRNormalization

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

attribute [instance] SmoothProjectiveCurveData.instCR SmoothProjectiveCurveData.instID
  SmoothProjectiveCurveData.instDVR SmoothProjectiveCurveData.instAlg
  SmoothProjectiveCurveData.instFR SmoothProjectiveCurveData.instAlgKR
  SmoothProjectiveCurveData.instScalarTower

namespace FunctionField_k

variable {k : Type*} [Field k]

variable {F₁ : Type*} {F₂ : Type*} [Field F₁] [Field F₂]

section Lemma18_11_Helpers

attribute [instance] DVROfFunctionField.isDVR DVROfFunctionField.isFractionRing

structure AbstractCurveIsomorphism
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (C : SmoothProjectiveCurveData k K n) where
  pointEquiv : C.P ≃ DVROfFunctionField k K
  localRing_compat : ∀ p, Set.range (algebraMap (C.R p) K) = ((pointEquiv p).valRing : Set K)
  forward_continuous : @Continuous C.P (DVROfFunctionField k K)
    C.zariskiTopology AbstractCurve.zariskiTopology pointEquiv

  regularFunctions_compat : ∀ (U : Set (DVROfFunctionField k K)),
    (AbstractCurve.regularFunctions U).carrier =
      C.regularFunctions (pointEquiv.symm '' U)

structure IsAbstractCurveIsomorphism
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (C : SmoothProjectiveCurveData k K n)
    (φ : C.P ≃ DVROfFunctionField k K) : Prop where
  localRing_eq : ∀ p, Set.range (algebraMap (C.R p) K) = ((φ p).valRing : Set K)
  regularFunctions_eq : ∀ (U : Set C.P) (f : K),
    f ∈ C.regularFunctions U ↔ f ∈ AbstractCurve.regularFunctions (φ '' U)

end Lemma18_11_Helpers
end FunctionField_k
end DVRNormalization
end ArithmeticGeometry
end
