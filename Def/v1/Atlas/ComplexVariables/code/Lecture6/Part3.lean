/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture6.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.MetricSpace.Basic
import Structure.v1.Atlas.ComplexVariables.code.Lecture6.Part2


namespace Lecture6

noncomputable def MoebiusTransformation.apply (T : MoebiusTransformation) (z : ℂ) : ℂ :=
  (T.a * z + T.b) / (T.c * z + T.d)

def MoebiusTransformation.MapsSetTo (T : MoebiusTransformation) (S₁ S₂ : Set ℂ) : Prop :=
  (∀ z ∈ S₁, T.c * z + T.d ≠ 0 → T.apply z ∈ S₂) ∧
  (∀ w ∈ S₂, ∃ z ∈ S₁, T.c * z + T.d ≠ 0 ∧ T.apply z = w)

def MoebiusTransformation.MapsCircle (T : MoebiusTransformation) (A B : Circle) : Prop :=
  T.MapsSetTo A.toSet B.toSet

def MoebiusTransformation.MapsGenCircle (T : MoebiusTransformation)
    (G₁ G₂ : GeneralizedCircle) : Prop :=
  T.MapsSetTo G₁.toSet G₂.toSet

noncomputable def MoebiusTransformation.comp (S T : MoebiusTransformation) :
    MoebiusTransformation where
  a := S.a * T.a + S.b * T.c
  b := S.a * T.b + S.b * T.d
  c := S.c * T.a + S.d * T.c
  d := S.c * T.b + S.d * T.d
  det_ne_zero := by
    have hS := S.det_ne_zero
    have hT := T.det_ne_zero
    have : (S.a * T.a + S.b * T.c) * (S.c * T.b + S.d * T.d) -
           (S.a * T.b + S.b * T.d) * (S.c * T.a + S.d * T.c) =
           (S.a * S.d - S.b * S.c) * (T.a * T.d - T.b * T.c) := by ring
    rw [this]
    exact mul_ne_zero hS hT


noncomputable def invTranslation (p : ℂ) : MoebiusTransformation where
  a := 0
  b := 1
  c := 1
  d := -p
  det_ne_zero := by
    simp only [zero_mul, one_mul, zero_sub]
    exact neg_ne_zero.mpr one_ne_zero

end Lecture6
