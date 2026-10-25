/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Discriminant
import Def.v1.Atlas.AlgebraicGeometryI.code.CoherentSheavesCurves.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CoherentSheavesCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannHurwitz
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalDivisorDecomposition
import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitz
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalDivisorDecomposition.Part4
import Structure.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitzFormula


noncomputable section

open Ideal Module

namespace RiemannHurwitzFormula

section DVRRamification

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

variable {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]

variable [Algebra R S]

/-- Construct `CurveMorphismData` for a degree-`n` cover of `ℙ¹`, where
`deg K_Y = -2`. -/
def CurveMorphismData.toP1 (n : ℤ) (deg_KX deg_R : ℤ)
    (h_nonneg : 0 ≤ deg_R) (h_pos : 0 < n) : CurveMorphismData where
  degree := n
  deg_KX := deg_KX
  deg_KY := -2
  deg_R := deg_R
  h_deg_R_nonneg := h_nonneg
  h_deg_pos := h_pos

/-- `CurveMorphismData` for a double cover `E → ℙ¹` realizing an elliptic curve. -/
def ellipticCurveP1Data : CurveMorphismData where
  degree := 2
  deg_KX := 0
  deg_KY := -2
  deg_R := 4
  h_deg_R_nonneg := by norm_num
  h_deg_pos := by norm_num

/-- `CurveMorphismData` for a hyperelliptic double cover of `ℙ¹` realizing a
curve of genus `g`, with `2g + 2` simple branch points. -/
def hyperellipticData (g : ℤ) (hg : 0 ≤ 2 * g + 2) : CurveMorphismData where
  degree := 2
  deg_KX := 2 * g - 2
  deg_KY := -2
  deg_R := 2 * g + 2
  h_deg_R_nonneg := hg
  h_deg_pos := by norm_num

end DVRRamification
end RiemannHurwitzFormula
end
