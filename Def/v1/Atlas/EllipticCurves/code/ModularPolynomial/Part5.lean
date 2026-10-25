/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.Algebra.CharP.Defs
import Def.v1.Atlas.EllipticCurves.code.ModularCurves.Part3
import Lemma.Complex.Atlas.v1.EllipticCurves.code.ModularCurves
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Uniformization
import Def.v1.Atlas.EllipticCurves.code.Uniformization
import Instance.v1.Atlas.EllipticCurves.code.ModularPolynomial
open scoped MatrixGroups UpperHalfPlane
open CongruenceSubgroup Complex


noncomputable section

open ModularFunction

section ModularCurveX0Defs

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup Matrix

open scoped MatrixGroups UpperHalfPlane

/-- The modular curve `X₀(N) = Γ₀(N) \ ℍ*` as the orbit space of `Γ₀(N)` acting on
the extended upper half-plane. -/
def ModularCurveX0 (N : ℕ) : Type :=
  MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 N) ExtendedUpperHalfPlane

/-- Canonical projection `ℍ* → X₀(N)`, sending a point to its `Γ₀(N)`-orbit. -/
def ModularCurveX0.mk (N : ℕ) : ExtendedUpperHalfPlane → ModularCurveX0 N :=
  Quotient.mk (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ExtendedUpperHalfPlane)

end ModularCurveX0Defs

namespace ModularFunctionField

open Polynomial hiding C X coeff_zero

/-- The modular `j`-function `ℍ → ℂ`, accessed inside the `ModularFunctionField`
namespace. -/
def jFunction : ℍ → ℂ := _root_.jFunction

/-- `f : ℍ → ℂ` is a rational function of `j(τ)` if there exist polynomials `p, q`
with `q ≠ 0` such that `q(j(τ)) · f(τ) = p(j(τ))` for all `τ ∈ ℍ`. -/
def HasCoeffsIn (f : LaurentSeries ℂ) (A : AddSubgroup ℂ) : Prop :=
  ∀ n : ℤ, f.coeff n ∈ A

/-- A function `f : ℍ → ℂ` has `q`-expansion coefficients in the additive subgroup
`A ⊆ ℂ`. -/
def PolynomialHasCoeffsIn (P : ℂ[X]) (A : AddSubgroup ℂ) : Prop :=
  ∀ k : ℕ, P.coeff k ∈ A

/-- If the `q`-expansion of `P(j)` has all coefficients in `A`, then so does `P`
itself. Proved by induction on the degree, peeling off leading terms. -/

end ModularFunctionField

namespace ModularPolynomial

open ModularFunctionField

/-- Scaling of the upper half-plane `τ ↦ N τ` (the level-`N` version inside the
`ModularPolynomial` namespace). -/
def scaleUHP (N : ℕ) (hN : 0 < N) (τ : ℍ) : ℍ :=
  ⟨(N : ℂ) * (τ : ℂ), by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, UpperHalfPlane.coe_im,
      UpperHalfPlane.coe_re, zero_mul, add_zero]
    exact mul_pos (Nat.cast_pos.mpr hN) τ.im_pos⟩

/-- The translate-and-scale map `τ ↦ (τ + k)/N`, used to describe the `Γ₀(N)`-orbit
representatives appearing in Lemma 19.16 and the conjugates of `j_N`. -/
def translateScaleUHP (N : ℕ) (hN : 0 < N) (k : ℤ) (τ : ℍ) : ℍ :=
  ⟨((τ : ℂ) + (k : ℂ)) / (N : ℂ), by
    have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hNc : ((N : ℂ) : ℂ) = ((N : ℝ) : ℂ) := by push_cast; ring
    rw [hNc, Complex.div_ofReal]
    show 0 < _ / _
    have him : (↑τ + ↑k : ℂ).im = τ.im := by
      simp [Complex.add_im, Complex.intCast_im]
    rw [him]
    exact div_pos τ.im_pos hN'⟩

/-- `j_N(τ) := j(N τ)`, the level-`N` `j`-function, here defined inside the
`ModularPolynomial` namespace. -/
def jFunc_N (N : ℕ) (hN : 0 < N) (τ : ℍ) : ℂ :=
  ModularFunctionField.jFunction (scaleUHP N hN τ)

/-- The conjugate `j_N`-value `j((τ + k)/N)`; these conjugates are the roots of
`Φ_N(j(τ), Y)` for `N` prime. -/
def jFunc_N_conjugate (N : ℕ) (hN : 0 < N) (k : ℤ) (τ : ℍ) : ℂ :=
  ModularFunctionField.jFunction (translateScaleUHP N hN k τ)

/-- The modular polynomial `Φ_N` viewed with complex coefficients, before checking
integrality (used to bootstrap Theorem 19.17). -/

end ModularPolynomial

section Lemma19_16

open ModularGroup

/-- Theorem 19.14 (restated): the degree of `Φ_N` in `Y` equals the Dedekind `ψ`
function, which is the index `[Γ(1) : Γ₀(N)]`. -/
def HasCyclicEndomorphism (F : Type*) [Field F] (N : ℕ) (j₀ : F) : Prop :=
  HasCyclicNIsogeny F N j₀ j₀

/-- The diagonal of Theorem 20.4: `Φ_N(j₀, j₀) = 0` iff the elliptic curve with
`j`-invariant `j₀` admits a cyclic endomorphism of degree `N`. -/

end ModularPolynomial

/-- A Laurent series `f : LaurentSeries ℂ` has integer coefficients: every
`f.coeff n` is in the image of `ℤ → ℂ`. -/
def HasIntCoeffs (f : LaurentSeries ℂ) : Prop :=
  ∀ n : ℤ, ∃ m : ℤ, f.coeff n = (m : ℂ)


end
