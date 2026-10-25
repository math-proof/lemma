/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.v1.Atlas.EllipticCurves.code.ModularCurves
open Manifold

open scoped ContDiff

/-- Definition 18.4 (Complex structure): a `ComplexStructure` on a topological space
`X` is a `ChartedSpace ℂ X` together with the property that `X` is a real-analytic
manifold modelled on `ℂ` (i.e., the transition maps between charts are holomorphic). -/


section Def1915_Prerequisites

open Def1811

open scoped MatrixGroups

namespace SL2Stabilizer

open ModularGroup

/-- The cube root of unity `ρ = -1/2 + i√3/2 ∈ ℍ`, one of the two elliptic points
(along with `i`) in the standard fundamental domain `𝓕`. -/
noncomputable def ρ : UpperHalfPlane :=
  ⟨-1/2 + Complex.I * (Real.sqrt 3 / 2), by
    simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im, Complex.I_re,
      Complex.ofReal_re]⟩

/-- The translate `ρ' = ρ + 1 = 1/2 + i√3/2 ∈ ℍ`, the other corner of the fundamental
domain `𝓕`. -/
noncomputable def ρ' : UpperHalfPlane := (1 : ℝ) +ᵥ ρ

/-- Part of Lemma 18.7: for a generic point `z` in the fundamental domain (not `i`,
`ρ`, or `ρ'`), its `SL₂(ℤ)`-stabilizer is the center `{±I}`, isomorphic to `ℤ/2ℤ`. -/

end SL2Stabilizer

section Lemma181

open ModularGroup UpperHalfPlane Complex Set Matrix SpecialLinearGroup

open scoped MatrixGroups

set_option maxHeartbeats 1600000

/-- The Cayley-type uniformizer `δ_x(τ) = (τ - τ_x)/(τ - conj(τ_x))` mapping the upper
half-plane biholomorphically to the open unit disk, sending `τ_x ↦ 0`. Used in
Lemma 18.8 to transfer disk automorphism rigidity to the upper half-plane. -/
noncomputable def deltaMap (τ_x : ℍ) (τ : ℂ) : ℂ :=
  (τ - (τ_x : ℂ)) / (τ - starRingEnd ℂ (τ_x : ℂ))

end Lemma181
end Def1915_Prerequisites
