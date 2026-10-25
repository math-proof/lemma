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
import Structure.v1.Atlas.ArithmeticGeometry.code.CurveTheory.Part6


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

def DVROfFunctionField.localRing (P : DVROfFunctionField k F) : ValuationSubring F :=
  P.valRing

def DVROfFunctionField.vanishesAt (P : DVROfFunctionField k F) (f : F) : Prop :=
  ∃ (hf : f ∈ P.valRing), ¬IsUnit (⟨f, hf⟩ : P.valRing)

def AbstractCurve.regularFunctions (U : Set (DVROfFunctionField k F)) : Subring F where
  carrier := {f : F | ∀ P ∈ U, f ∈ P.valRing}
  mul_mem' hf hg P hP := P.valRing.toSubring.mul_mem (hf P hP) (hg P hP)
  one_mem' P _ := P.valRing.toSubring.one_mem
  add_mem' hf hg P hP := P.valRing.toSubring.add_mem (hf P hP) (hg P hP)
  zero_mem' P _ := P.valRing.toSubring.zero_mem
  neg_mem' hf P hP := P.valRing.toSubring.neg_mem (hf P hP)

def AbstractCurve.zeroLocus (S : Set F) : Set (DVROfFunctionField k F) :=
  {P | ∀ f ∈ S, P.vanishesAt f}

end Lemma18_11_Helpers
end FunctionField_k
end DVRNormalization
end ArithmeticGeometry
end
