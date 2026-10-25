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
open scoped MatrixGroups UpperHalfPlane
open CongruenceSubgroup Complex


noncomputable section

namespace ModularFunction

/-- The upper half-plane as a subset of `ℂ`: complex numbers with strictly positive
imaginary part. -/
def upperHalfPlaneSet : Set ℂ := {z : ℂ | 0 < z.im}

/-- The local uniformizer `q_N(τ) = exp(2πiτ/N)` at the cusp `i∞` for level `N`. -/
def qMapN (N : ℕ) (τ : ℍ) : ℂ :=
  Complex.exp (2 * ↑Real.pi * Complex.I * (τ : ℂ) / (N : ℂ))

/-- `f : ℍ → ℂ` is meromorphic at the cusp `i∞` if, after the substitution
`q = q_N(τ)`, it agrees near `0` with a meromorphic function in `q`. -/
def IsMeromorphicAtInfty (f : ℍ → ℂ) : Prop :=
  ∃ (N : ℕ) (_ : 0 < N) (g : ℂ → ℂ), MeromorphicAt g 0 ∧
    ∀ᶠ τ : ℍ in UpperHalfPlane.atImInfty, f τ = g (qMapN N τ)

/-- `f : ℍ → ℂ` is meromorphic at every cusp (= every `SL₂(ℤ)`-translate of `i∞`). -/
def IsMeromorphicAtCusps (f : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), IsMeromorphicAtInfty (fun τ => f (γ • τ))

/-- `f : ℍ → ℂ` is meromorphic on the upper half-plane if it extends to a meromorphic
function on the open set `{Im z > 0} ⊆ ℂ`. -/
def IsMeromorphicOnH (f : ℍ → ℂ) : Prop :=
  ∃ g : ℂ → ℂ, MeromorphicOn g upperHalfPlaneSet ∧
    ∀ τ : ℍ, g (τ : ℂ) = f τ

/-- `f` is invariant under the subgroup `Γ ≤ SL₂(ℤ)`, i.e. `f(γ τ) = f(τ)` for
all `γ ∈ Γ` and `τ ∈ ℍ`. -/
def IsInvariantUnder (f : ℍ → ℂ) (Γ : Subgroup SL(2, ℤ)) : Prop :=
  ∀ (γ : SL(2, ℤ)), γ ∈ Γ → ∀ (τ : ℍ), f (γ • τ) = f τ

/-- `f : ℍ → ℂ` is holomorphic on the upper half-plane if it extends to an analytic
function on the open set `{Im z > 0} ⊆ ℂ`. -/
def IsHolomorphicOnH (f : ℍ → ℂ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g upperHalfPlaneSet ∧
    ∀ τ : ℍ, g (τ : ℂ) = f τ

/-- The modular `j`-function `j : ℍ → ℂ`. -/
def jModular : ℍ → ℂ := jFunction

/-- The `j`-function is meromorphic on the upper half-plane (in fact holomorphic). -/
def scaleUHP (N : ℕ) (hN : 0 < N) (τ : ℍ) : ℍ :=
  ⟨(N : ℂ) * (τ : ℂ), by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im]
    simp [mul_pos (Nat.cast_pos.mpr hN) τ.im_pos]⟩

/-- The level-`N` `j`-function `j_N(τ) := j(N τ)` (cf. Theorem 19.13). -/
def jModularN (N : ℕ) (hN : 0 < N) (τ : ℍ) : ℂ :=
  jModular (scaleUHP N hN τ)

end ModularFunction
end
