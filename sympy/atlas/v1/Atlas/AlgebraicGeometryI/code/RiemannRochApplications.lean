/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochApplications.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.RiemannRochEulerCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochEulerCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochRiemannForm
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.DedekindCurve
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.RiemannRochRiemannForm
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.DedekindCurve

open CanonicalSheafCurves RiemannRochEulerCurves RiemannRochRiemannForm
open SheafCohCurvesFiniteness

noncomputable section

namespace RiemannRochApplications

/-- Serre duality package for the structure sheaf `𝒪_C` of a smooth complete
curve `C`: `h^0(𝒪) = 1`, `h^1(𝒪) = g`. -/
def structureSheafSD (C : SmoothCompleteCurve) (hg : C.g ≥ 0) :
    SerreDualityCurve C 1 0 where
  h0 := 1
  h1 := C.g
  h0_dual := C.χ (1, C.degK) + 1
  chi_decomp := by
    rw [chi_structure_sheaf_curve]
  serre_dual := by


    have := euler_char_canonical C
    linarith
  h0_nonneg := by norm_num
  h1_nonneg := hg

/-- Serre duality package for the canonical sheaf `ω_C`: `h^0(ω) = g`,
`h^1(ω) = 1`. -/
def canonicalSheafSD (C : SmoothCompleteCurve) (hg : C.g ≥ 0) :
    SerreDualityCurve C 1 C.degK where
  h0 := C.g
  h1 := 1
  h0_dual := C.χ (1, 0) + C.g
  chi_decomp := by
    rw [euler_char_canonical]
  serre_dual := by


    have := chi_structure_sheaf_curve C
    linarith
  h0_nonneg := hg
  h1_nonneg := by norm_num

/-- Serre duality package for `𝒪` derived from a Dedekind curve `C` with
`ddGenus` providing `h^1(𝒪)`. -/
def serreDualityO_fromDedekind {k : Type*} [Field k] (C : DedekindCurve k) :
    SerreDualityCurve C.toSmoothCompleteCurve 1 0 where
  h0 := 1
  h1 := C.ddGenus
  h0_dual := C.ddGenus
  chi_decomp := by
    rw [chi_structure_sheaf_curve]

    rfl
  serre_dual := rfl
  h0_nonneg := by norm_num
  h1_nonneg := Nat.cast_nonneg _

/-- Serre duality package for `ω_C` derived from a Dedekind curve `C`. -/
def serreDualityK_fromDedekind {k : Type*} [Field k] (C : DedekindCurve k) :
    SerreDualityCurve C.toSmoothCompleteCurve 1 C.toSmoothCompleteCurve.degK where
  h0 := C.ddGenus
  h1 := 1
  h0_dual := 1
  chi_decomp := by
    rw [euler_char_canonical]

    rfl
  serre_dual := rfl
  h0_nonneg := Nat.cast_nonneg _
  h1_nonneg := by norm_num

end RiemannRochApplications

end
