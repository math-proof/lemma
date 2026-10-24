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
import sympy.atlas.v1.Atlas.EllipticCurves.code.ModularCurves
import Lemma.Complex.Atlas.v1.EllipticCurves.code.ModularCurves
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Uniformization
import sympy.atlas.v1.Atlas.EllipticCurves.code.Uniformization

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

open ModularFunction

/-- A modular function for the congruence subgroup `Γ` (Definition 19.2): a function
`f : ℍ → ℂ` that is meromorphic on `ℍ`, `Γ`-invariant, and meromorphic at the cusps. -/
structure IsModularFunction (f : ℍ → ℂ) (Γ : Subgroup SL(2, ℤ)) : Prop where
  meromorphicOnH : IsMeromorphicOnH f
  invariant : IsInvariantUnder f Γ
  meromorphicAtCusps : IsMeromorphicAtCusps f

namespace ModularFunction

/-- Auxiliary version of Theorem 19.8: every modular function for `Γ(1) = SL₂(ℤ)` is
a rational function of `j(τ)`, witnessed by a pair `(P, Q)` of polynomials. -/
end ModularFunction

/-- The level-`N` `j`-function `j_N` is meromorphic on `ℍ`: it is the composition of
`j` with the (holomorphic) scaling `τ ↦ N τ`. -/
namespace ModularPolynomial

/-- The (classical) modular polynomial `Φ_N(X, Y) ∈ ℤ[X, Y]` as a `MvPolynomial`
indexed by `Fin 2`, characterized in Definition 19.15 as the minimal polynomial of
`j_N` over `ℂ(j)`. -/
def HasCyclicNIsogeny (F : Type*) [Field F] (N : ℕ) (j₁ j₂ : F) : Prop :=
  ∃ (E₁ E₂ : WeierstrassCurve.Affine F) (_ : E₁.IsElliptic) (_ : E₂.IsElliptic),
    E₁.j = j₁ ∧ E₂.j = j₂ ∧
    ∃ (φ : E₁.Point →+ E₂.Point), Function.Surjective φ ∧
      ∃ (P : E₁.Point), addOrderOf P = N ∧
        ∀ Q : E₁.Point, φ Q = 0 → ∃ k : ℤ, Q = k • P

/-- Theorem 20.7: the modular polynomial is symmetric, `Φ_N(X, Y) = Φ_N(Y, X)`. -/
def dedekindPsi (N : ℕ) : ℕ :=
  if N = 0 then 0
  else ∏ p ∈ N.primeFactors, p ^ (N.factorization p - 1) * (p + 1)

/-- Theorem 19.14: the degree of `Φ_N` in the variable `Y` equals
`[Γ(1) : Γ₀(N)] = ψ(N)`. -/
end ModularPolynomial

namespace ModularFunction

/-- Corollary 19.10: every modular function for `Γ(1)` that is holomorphic on `ℍ` is a
polynomial in `j(τ)`. The witness `P` is constructed from a rational-function
representation by checking that the denominator polynomial has degree `0`. -/
end ModularFunction

section ModularCurveX0Defs

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup Matrix
open scoped MatrixGroups UpperHalfPlane

/-- The `(i, j)`-entry of an `SL₂(ℤ)`-matrix, coerced to `ℚ`. -/
def sl2zEntry (γ : SL(2, ℤ)) (i j : Fin 2) : ℚ :=
  ((↑γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ)

/-- The determinant identity `ad - bc = 1` rewritten in terms of `sl2zEntry`. -/
lemma sl2zEntry_det (γ : SL(2, ℤ)) :
    sl2zEntry γ 0 0 * sl2zEntry γ 1 1 - sl2zEntry γ 0 1 * sl2zEntry γ 1 0 = 1 := by
  simp only [sl2zEntry]
  have hd := γ.det_coe
  rw [det_fin_two] at hd
  exact_mod_cast hd

/-- The matrix-product entry formula `(g₁ g₂)_{ij} = g₁_{i0} g₂_{0j} + g₁_{i1} g₂_{1j}`
for `SL₂(ℤ)`-matrices, expressed via `sl2zEntry`. -/
lemma sl2zEntry_mul (g₁ g₂ : SL(2, ℤ)) (i j : Fin 2) :
    sl2zEntry (g₁ * g₂) i j =
    sl2zEntry g₁ i 0 * sl2zEntry g₂ 0 j + sl2zEntry g₁ i 1 * sl2zEntry g₂ 1 j := by
  simp only [sl2zEntry]
  simp [mul_apply, Fin.sum_univ_two]

/-- The extended upper half-plane `ℍ*` = `ℍ ⊔ ℚ ∪ {∞}`, obtained by adjoining the
rational cusps and the cusp at infinity to `ℍ`. -/
def ExtendedUpperHalfPlane := ℍ ⊕ (WithTop ℚ)

namespace ExtendedUpperHalfPlane

/-- Inclusion `ℍ ↪ ℍ*`. -/
def ofUHP (τ : ℍ) : ExtendedUpperHalfPlane := Sum.inl τ

/-- Inclusion of a rational cusp `r ∈ ℚ ↪ ℍ*`. -/
def ofRat (r : ℚ) : ExtendedUpperHalfPlane := Sum.inr (↑r)

/-- The cusp at infinity in `ℍ*`. -/
def cuspInfty : ExtendedUpperHalfPlane := Sum.inr ⊤

/-- The action of `SL₂(ℤ)` on the cusps `ℚ ∪ {∞}`, given by the linear-fractional
formula `γ · r = (ar + b)/(cr + d)` and `γ · ∞ = a/c` (with `c = 0` mapping to `∞`). -/
def cuspAction (γ : SL(2, ℤ)) : WithTop ℚ → WithTop ℚ
  | ⊤ => if sl2zEntry γ 1 0 = 0 then ⊤ else ↑(sl2zEntry γ 0 0 / sl2zEntry γ 1 0)
  | (r : ℚ) => if sl2zEntry γ 1 0 * r + sl2zEntry γ 1 1 = 0 then ⊤
      else ↑((sl2zEntry γ 0 0 * r + sl2zEntry γ 0 1) / (sl2zEntry γ 1 0 * r + sl2zEntry γ 1 1))

/-- The identity matrix acts trivially on the cusps. -/
theorem cuspAction_one : ∀ x, cuspAction 1 x = x := by
  intro x
  cases x with
  | top => simp [cuspAction, sl2zEntry]
  | coe r => simp [cuspAction, sl2zEntry]

/-- Auxiliary algebraic identity used in proving the multiplicative law for
`cuspAction`: handles the case where the denominator vanishes for `g₂`. -/
lemma cuspAction_factor_denom_zero (g₁ g₂ : SL(2, ℤ)) (r : ℚ)
    (hd₂ : sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1 = 0) :
    sl2zEntry (g₁ * g₂) 1 0 * r + sl2zEntry (g₁ * g₂) 1 1 =
    sl2zEntry g₁ 1 0 * (sl2zEntry g₂ 0 0 * r + sl2zEntry g₂ 0 1) := by
  rw [sl2zEntry_mul, sl2zEntry_mul]
  have : sl2zEntry g₁ 1 1 * (sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1) = 0 := by
    rw [hd₂, mul_zero]
  linarith

/-- Companion identity to `cuspAction_factor_denom_zero` for the numerator. -/
lemma cuspAction_factor_numer_zero (g₁ g₂ : SL(2, ℤ)) (r : ℚ)
    (hd₂ : sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1 = 0) :
    sl2zEntry (g₁ * g₂) 0 0 * r + sl2zEntry (g₁ * g₂) 0 1 =
    sl2zEntry g₁ 0 0 * (sl2zEntry g₂ 0 0 * r + sl2zEntry g₂ 0 1) := by
  rw [sl2zEntry_mul, sl2zEntry_mul]
  have : sl2zEntry g₁ 0 1 * (sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1) = 0 := by
    rw [hd₂, mul_zero]
  linarith

/-- If the denominator of the linear-fractional action of `g₂` on `r` vanishes, then
the numerator cannot also vanish (consequence of `det g₂ = 1`). -/
lemma cuspAction_numer_ne_zero_of_denom_zero (g₂ : SL(2, ℤ)) (r : ℚ)
    (hd₂ : sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1 = 0) :
    sl2zEntry g₂ 0 0 * r + sl2zEntry g₂ 0 1 ≠ 0 := by
  intro heq
  have hdet := sl2zEntry_det g₂
  have : sl2zEntry g₂ 0 0 * (sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1) -
    sl2zEntry g₂ 1 0 * (sl2zEntry g₂ 0 0 * r + sl2zEntry g₂ 0 1) = 1 := by linarith
  rw [hd₂, heq, mul_zero, mul_zero, sub_zero] at this
  exact zero_ne_one this

set_option maxHeartbeats 400000 in
/-- The cusp action at `∞` is compatible with multiplication in `SL₂(ℤ)`:
`(g₁ g₂) · ∞ = g₁ · (g₂ · ∞)`. -/
theorem cuspAction_mul_top (g₁ g₂ : SL(2, ℤ)) :
    cuspAction (g₁ * g₂) ⊤ = cuspAction g₁ (cuspAction g₂ ⊤) := by
  simp only [cuspAction]
  by_cases hc₂ : sl2zEntry g₂ 1 0 = 0
  · simp only [hc₂, ite_true]
    rw [sl2zEntry_mul]
    simp only [hc₂, mul_zero, add_zero]
    have ha₂ : sl2zEntry g₂ 0 0 ≠ 0 := by
      intro heq
      have := sl2zEntry_det g₂
      rw [hc₂, mul_zero, sub_zero, heq, zero_mul] at this
      exact zero_ne_one this
    by_cases hc₁ : sl2zEntry g₁ 1 0 = 0
    · simp [hc₁]
    · simp only [mul_ne_zero hc₁ ha₂, ite_false, hc₁]
      rw [sl2zEntry_mul]
      simp only [hc₂, mul_zero, add_zero]
      congr 1
      field_simp
  · simp only [hc₂, ite_false]
    rw [sl2zEntry_mul, sl2zEntry_mul]
    by_cases hdenom : sl2zEntry g₁ 1 0 * (sl2zEntry g₂ 0 0 / sl2zEntry g₂ 1 0) +
        sl2zEntry g₁ 1 1 = 0
    · have : sl2zEntry g₁ 1 0 * sl2zEntry g₂ 0 0 +
          sl2zEntry g₁ 1 1 * sl2zEntry g₂ 1 0 = 0 := by
        field_simp at hdenom
        linarith
      simp [this, hdenom]
    · have hne : sl2zEntry g₁ 1 0 * sl2zEntry g₂ 0 0 +
          sl2zEntry g₁ 1 1 * sl2zEntry g₂ 1 0 ≠ 0 := by
        intro heq
        apply hdenom
        field_simp
        linarith
      simp only [hne, hdenom, ite_false]
      congr 1
      field_simp

set_option maxHeartbeats 800000 in
/-- The cusp action at a rational cusp `r` is compatible with multiplication in
`SL₂(ℤ)`: `(g₁ g₂) · r = g₁ · (g₂ · r)`. -/
theorem cuspAction_mul_coe (g₁ g₂ : SL(2, ℤ)) (r : ℚ) :
    cuspAction (g₁ * g₂) ↑r = cuspAction g₁ (cuspAction g₂ ↑r) := by
  simp only [cuspAction]
  by_cases hd₂ : sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1 = 0
  · simp only [hd₂, ite_true]
    have hc₂_ne : sl2zEntry g₂ 1 0 ≠ 0 := by
      intro heq
      rw [heq, zero_mul, zero_add] at hd₂
      have := sl2zEntry_det g₂
      rw [hd₂, heq] at this
      simp at this
    have hnum₂_ne := cuspAction_numer_ne_zero_of_denom_zero g₂ r hd₂
    rw [cuspAction_factor_denom_zero g₁ g₂ r hd₂,
        cuspAction_factor_numer_zero g₁ g₂ r hd₂]
    by_cases hc₁ : sl2zEntry g₁ 1 0 = 0
    · simp [hc₁]
    · simp only [mul_ne_zero hc₁ hnum₂_ne, ite_false, hc₁]
      congr 1
      field_simp
  · simp only [hd₂, ite_false]
    set s := (sl2zEntry g₂ 0 0 * r + sl2zEntry g₂ 0 1) /
             (sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1) with hs_def
    have hdenom_rel : sl2zEntry g₁ 1 0 * s + sl2zEntry g₁ 1 1 =
        (sl2zEntry (g₁ * g₂) 1 0 * r + sl2zEntry (g₁ * g₂) 1 1) /
        (sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1) := by
      rw [hs_def, sl2zEntry_mul, sl2zEntry_mul]
      have hd₂' : r * sl2zEntry g₂ 1 0 + sl2zEntry g₂ 1 1 ≠ 0 := by
        rwa [show r * sl2zEntry g₂ 1 0 + sl2zEntry g₂ 1 1 =
             sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1 from by ring]
      field_simp
      ring
    have zero_iff : sl2zEntry g₁ 1 0 * s + sl2zEntry g₁ 1 1 = 0 ↔
        sl2zEntry (g₁ * g₂) 1 0 * r + sl2zEntry (g₁ * g₂) 1 1 = 0 := by
      rw [hdenom_rel, div_eq_zero_iff]
      exact ⟨fun h => h.resolve_right hd₂, fun h => Or.inl h⟩
    by_cases hprod : sl2zEntry (g₁ * g₂) 1 0 * r + sl2zEntry (g₁ * g₂) 1 1 = 0
    · have : sl2zEntry g₁ 1 0 * s + sl2zEntry g₁ 1 1 = 0 := zero_iff.mpr hprod
      simp [hprod, this]
    · have hne : sl2zEntry g₁ 1 0 * s + sl2zEntry g₁ 1 1 ≠ 0 :=
        fun h => hprod (zero_iff.mp h)
      simp only [hprod, hne, ite_false]
      congr 1
      rw [hs_def, sl2zEntry_mul, sl2zEntry_mul, sl2zEntry_mul, sl2zEntry_mul]
      have hd₂' : r * sl2zEntry g₂ 1 0 + sl2zEntry g₂ 1 1 ≠ 0 := by
        rwa [show r * sl2zEntry g₂ 1 0 + sl2zEntry g₂ 1 1 =
             sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1 from by ring]
      field_simp
      ring

/-- Multiplicativity of the cusp action on all of `WithTop ℚ`, combining the cases
for the cusp at infinity and the finite rational cusps. -/
theorem cuspAction_mul (g₁ g₂ : SL(2, ℤ)) :
    ∀ x, cuspAction (g₁ * g₂) x = cuspAction g₁ (cuspAction g₂ x) := by
  intro x
  cases x with
  | top => exact cuspAction_mul_top g₁ g₂
  | coe r => exact cuspAction_mul_coe g₁ g₂ r

/-- The `SL₂(ℤ)`-action on `ℍ*`, defined cases-wise: the Möbius action on the upper
half-plane component, and `cuspAction` on the cusp component. -/
def smulExt (γ : SL(2, ℤ)) (x : ExtendedUpperHalfPlane) : ExtendedUpperHalfPlane :=
  match x with
  | Sum.inl τ => Sum.inl (γ • τ)
  | Sum.inr c => Sum.inr (cuspAction γ c)

/-- Register `smulExt` as the scalar multiplication of `SL₂(ℤ)` on `ℍ*`. -/
instance : SMul SL(2, ℤ) ExtendedUpperHalfPlane where
  smul := smulExt

/-- The `SL₂(ℤ)`-action on `ℍ*` is a `MulAction`, with `1 · x = x` and
`(g₁ g₂) · x = g₁ · (g₂ · x)`. -/
instance : MulAction SL(2, ℤ) ExtendedUpperHalfPlane where
  one_smul x := by
    show smulExt 1 x = x
    cases x with
    | inl τ =>
      show Sum.inl ((1 : SL(2, ℤ)) • τ) = Sum.inl τ
      simp [one_smul]
    | inr c =>
      show Sum.inr (cuspAction 1 c) = Sum.inr c
      simp [cuspAction_one]
  mul_smul g₁ g₂ x := by
    show smulExt (g₁ * g₂) x = smulExt g₁ (smulExt g₂ x)
    cases x with
    | inl τ =>
      show Sum.inl ((g₁ * g₂) • τ) = Sum.inl (g₁ • (g₂ • τ))
      congr 1
      exact SemigroupAction.mul_smul g₁ g₂ τ
    | inr c =>
      show Sum.inr (cuspAction (g₁ * g₂) c) = Sum.inr (cuspAction g₁ (cuspAction g₂ c))
      congr 1
      exact cuspAction_mul g₁ g₂ c

/-- Restriction of the `SL₂(ℤ)`-action on `ℍ*` to the congruence subgroup `Γ₀(N)`. -/
instance gamma0Action (N : ℕ) :
    MulAction (CongruenceSubgroup.Gamma0 N) ExtendedUpperHalfPlane :=
  MulAction.compHom ExtendedUpperHalfPlane (CongruenceSubgroup.Gamma0 N).subtype

end ExtendedUpperHalfPlane

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


/-- Corollary 19.6 (integrality part): the `q`-expansion of `j(τ)` has all integer
coefficients. -/
end
