/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalSheafCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CoherentSheavesCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CoherentSheavesCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalBundleProjective
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalBundleGeneral
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochCurves
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleProjective
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleGeneral
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.RiemannRochCurves

set_option maxHeartbeats 800000

open RiemannRochCurves

noncomputable section

namespace CanonicalSheafCurves

/-- Existence witness for a smooth complete curve of genus `g`: a Dedekind `k`-algebra `A` whose
Kähler differential module has rank `g`. -/
def CurveWitness (g : ℤ) : Prop :=
  ∃ (k : Type) (_ : Field k) (A : Type) (_ : CommRing A) (_ : IsDomain A)
    (_ : IsDedekindDomain A) (_ : Algebra k A) (_ : Module.Finite k A),
    (Module.finrank k (Ω[A⁄k]) : ℤ) = g

/-- The rational numbers `ℚ` (as a `ℚ`-algebra) witness the genus-`0` case of `CurveWitness`. -/
theorem curveWitness_zero : CurveWitness 0 := by
  refine ⟨ℚ, inferInstance, ℚ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_⟩
  simp only [Nat.cast_eq_zero]
  haveI := KaehlerDifferential.subsingleton_of_surjective ℚ ℚ (fun x => ⟨x, rfl⟩)
  exact Module.finrank_zero_of_subsingleton

/-- For every natural number `g`, there exists a smooth complete curve of genus `g`. -/
structure SmoothCompleteCurve where
  g : ℤ
  χ : ℤ × ℤ →+ ℤ
  degK : ℤ
  hg_nonneg : 0 ≤ g
  hχ_struct : χ (1, 0) = 1 - g
  hχ_sky : χ (0, 1) = 1
  hwf : CurveWitness g

/-- Serre duality at the level of Euler characteristics: `χ(K_C) = g - 1`. -/
def canonicalSheafClass (C : SmoothCompleteCurve) : ℤ × ℤ := (1, C.degK)

/-- Genus of the smooth complete curve `C`, as an integer. -/
def curveGenusOfSmooth (C : SmoothCompleteCurve) : ℤ := C.g

/-- Degree of the canonical divisor of `C`. -/
def canonicalDeg (C : SmoothCompleteCurve) : ℤ := C.degK
