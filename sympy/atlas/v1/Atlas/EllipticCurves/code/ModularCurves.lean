/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Manifold

open scoped ContDiff

/-- Definition 18.4 (Complex structure): a `ComplexStructure` on a topological space
`X` is a `ChartedSpace ℂ X` together with the property that `X` is a real-analytic
manifold modelled on `ℂ` (i.e., the transition maps between charts are holomorphic). -/
namespace Def1811

/-- The reduction-mod-`N` group homomorphism `SL₂(ℤ) → SL₂(ℤ/Nℤ)`. -/
noncomputable def SL2_reductionMod (N : ℕ) : SL(2, ℤ) →* SL(2, ZMod N) :=
  SpecialLinearGroup.map (Int.castRingHom (ZMod N))

/-- Definition 18.11: the principal congruence subgroup `Γ(N) ⊆ SL₂(ℤ)`, consisting of
matrices congruent to the identity modulo `N`. -/
def PrincipalCongruenceSubgroup (N : ℕ) : Subgroup SL(2, ℤ) :=
  CongruenceSubgroup.Gamma N

/-- The Hecke-type congruence subgroup `Γ₀(N) ⊆ SL₂(ℤ)` of matrices that are upper
triangular modulo `N`. -/
def CongruenceSubgroup0 (N : ℕ) : Subgroup SL(2, ℤ) :=
  CongruenceSubgroup.Gamma0 N

/-- The Hecke-type congruence subgroup `Γ₁(N) ⊆ SL₂(ℤ)` of matrices that are
upper-unitriangular modulo `N`. -/
def CongruenceSubgroup1 (N : ℕ) : Subgroup SL(2, ℤ) :=
  CongruenceSubgroup.Gamma1 N

/-- Definition 18.11: a subgroup `H ⊆ SL₂(ℤ)` is a *congruence subgroup* if it
contains some principal congruence subgroup `Γ(N)`. -/
def IsCongruenceSubgroup (H : Subgroup SL(2, ℤ)) : Prop :=
  CongruenceSubgroup.IsCongruenceSubgroup H

/-- The open modular curve `Y_Γ := Γ \ ℍ`, the quotient of the upper half-plane by a
congruence subgroup `Γ`. -/
noncomputable def ModularCurveOpen (Γ : Subgroup SL(2, ℤ)) : Type :=
  Quotient (MulAction.orbitRel Γ UpperHalfPlane)

/-- The extended upper half-plane `ℍ* = ℍ ∪ ℚ ∪ {∞}` (cusps adjoined), modelled here
as an `opaque` type pending a formal definition. -/
opaque ExtendedUpperHalfPlane : Type

/-- Axiom: there is a natural `SL₂(ℤ)`-action on `ℍ*`. -/
noncomputable def ModularCurve (Γ : Subgroup SL(2, ℤ)) : Type :=
  Quotient (MulAction.orbitRel Γ ExtendedUpperHalfPlane)

end Def1811

section Def1915_Prerequisites

open Def1811

open scoped MatrixGroups

/-- The full modular curve `X(1) = SL₂(ℤ) \ ℍ*`. -/
noncomputable abbrev X1 : Type :=
  Quotient (MulAction.orbitRel SL(2, ℤ) ExtendedUpperHalfPlane)

/-- The topology on `X(1)` inherited as a quotient of `ℍ*`. -/
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

/-- A combinatorial triangulation of a topological space, recording the number of
vertices `V`, edges `E`, faces `F`, and genus `g`, subject to the Euler characteristic
identity `V - E + F = 2 - 2g`. -/
structure Triangulation (X : Type*) [TopologicalSpace X] where
  V : ℕ
  E : ℕ
  F : ℕ
  g : ℕ
  euler : V + F + 2 * g = E + 2

/-- An explicit triangulation of `X(1)` with `V = 3, E = 3, F = 2`, giving genus `0`
(the three vertices being the orbits of `i, ρ, ∞`). -/
noncomputable def X1.triangulation : Triangulation X1 where
  V := 3
  E := 3
  F := 2
  g := 0
  euler := by norm_num
