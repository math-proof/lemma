/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Isogenies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.PurelyInseparable.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.EllipticCurves
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.EllipticCurves
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.PadicElliptic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.PadicElliptic
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.WeierstrassValBound

open WeierstrassCurve

namespace EllipticCurveIsogeny

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F}
    [W₁.IsElliptic] [W₂.IsElliptic]

end EllipticCurveIsogeny

namespace EllipticCurveIsogeny

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F}
    [W₁.IsElliptic] [W₂.IsElliptic]

end EllipticCurveIsogeny

namespace EllipticCurveIsogeny

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F}
    [W₁.IsElliptic] [W₂.IsElliptic]

end EllipticCurveIsogeny

namespace EllipticCurveIsogeny

variable {k : Type*} [Field k] [DecidableEq k]
    {W₁ W₂ : WeierstrassCurve k} [W₁.IsElliptic] [W₂.IsElliptic]

/-- The function-field extension data associated to an isogeny $\varphi$: a pair of
fields $k(E_1) \supseteq \varphi^* k(E_2)$ with the inclusion as an algebra map. -/
namespace FunctionFieldExtension

variable {φ : EllipticCurveIsogeny W₁ W₂} (ext : φ.FunctionFieldExtension)

/-- The "top" field $k(E_1)$ is a field. -/
instance : Field ext.FunctionField := ext.field_top
/-- The "bottom" field $\varphi^* k(E_2)$ is a field. -/
instance : Field ext.PullbackField := ext.field_bot
/-- $k(E_1)$ is an algebra over the pullback field $\varphi^* k(E_2)$. -/
instance : Algebra ext.PullbackField ext.FunctionField := ext.algebra_inst

end FunctionFieldExtension

/-- An isogeny is separable if the induced function-field extension is separable. -/
end EllipticCurveIsogeny

namespace EllipticCurveIsogeny

universe u


/-- An isogeny respects negation: $\varphi(-P) = -\varphi(P)$ (corollary of being
a group homomorphism). -/
end EllipticCurveIsogeny

section PointFinite

variable {R : Type*} [CommRing R] [Fintype R] (W : WeierstrassCurve R)

/-- Encode an affine Weierstrass point as `Option (R × R)`: the point at infinity is
`none`, and an affine point $(x, y)$ is `some (x, y)`. -/
noncomputable def WeierstrassCurve.Affine.Point.toOption
    (P : W.toAffine.Point) : Option (R × R) :=
  match P with
  | .zero => Option.none
  | .some x y _ => Option.some (x, y)

omit [Fintype R] in
/-- The encoding `toOption` is injective: distinct affine points have distinct
encodings. -/
lemma WeierstrassCurve.Affine.Point.toOption_injective :
    Function.Injective (WeierstrassCurve.Affine.Point.toOption W) := by
  intro a b hab
  simp only [WeierstrassCurve.Affine.Point.toOption] at hab
  cases a <;> cases b <;> simp_all

/-- If the base ring is finite, then the set of points of an affine Weierstrass curve
is also finite. -/
noncomputable instance WeierstrassCurve.Affine.Point.finite :
    Finite W.toAffine.Point :=
  Finite.of_injective _ (WeierstrassCurve.Affine.Point.toOption_injective W)

end PointFinite


/-- An elliptic curve over $\mathbb{Q}$ has good reduction at a prime $p$ if it
admits a model that reduces mod $p$ to an elliptic curve over $\mathbb{F}_p$. -/
structure HasGoodReduction (W : WeierstrassCurve ℚ) (p : ℕ) [Fact (Nat.Prime p)] where
  reducedCurve : WeierstrassCurve (ZMod p)
  isElliptic : reducedCurve.IsElliptic
open scoped Classical in
/-- Variant of Corollary 24.10 over an algebraic closure: $E(\bar k)[n]$ is finite. -/
noncomputable instance baseChange_padic_isElliptic
    {p : ℕ} [Fact (Nat.Prime p)]
    {W : WeierstrassCurve ℚ} [W.IsElliptic] :
    (W.baseChange ℚ_[p]).IsElliptic := by
  constructor
  rw [show (W.baseChange ℚ_[p]).Δ = algebraMap ℚ ℚ_[p] W.Δ by
    simp [WeierstrassCurve.baseChange, WeierstrassCurve.Δ]]
  exact (algebraMap ℚ ℚ_[p]).isUnit_map ‹W.IsElliptic›.isUnit

/-- Membership in the $n$-th piece of the $p$-adic filtration on $E(\mathbb{Q}_p)$:
the point $O$ is always in, and an affine point $(x, y)$ lies in $E_n$ when $n = 0$
or when $y \neq 0$ and $v_p(x) - v_p(y) \geq n$. -/
def PadicFiltrationMem (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    (P : (W.baseChange ℚ_[p]).toAffine.Point) : Prop :=
  match P with
  | .zero => True
  | .some x y _ => n = 0 ∨ (y ≠ 0 ∧ (n : ℤ) ≤ Padic.valuation x - Padic.valuation y)


/-- The identity point lies in every piece $E_n$ of the $p$-adic filtration. -/
theorem PadicFiltrationMem.zero (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
    PadicFiltrationMem W p n (.zero) :=
  trivial

/-- The $p$-adic filtration on $E(\mathbb{Q}_p)$: a decreasing family of
subgroups $E = E_0 \supseteq E_1 \supseteq E_2 \supseteq \cdots$ defined via
the $p$-adic valuation, together with the (mild) assumptions
$a_1 = a_2 = a_3 = 0$ required for the addition-formula computations. -/
structure PadicFiltration (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (p : ℕ) [Fact (Nat.Prime p)] where
  group : ℕ → AddSubgroup (W.baseChange ℚ_[p]).toAffine.Point
  antitone : Antitone group
  mem_iff : ∀ n P, P ∈ group n ↔ PadicFiltrationMem W p n P
  zero_eq_top : group 0 = ⊤
  ha₁ : W.a₁ = 0
  ha₂ : W.a₂ = 0
  ha₃ : W.a₃ = 0

/-- The $p$-adic valuation is invariant under negation: $v_p(-x) = v_p(x)$. -/
lemma padic_valuation_neg {p : ℕ} [Fact (Nat.Prime p)] (x : ℚ_[p]) (hx : x ≠ 0) :
    Padic.valuation (-x) = Padic.valuation x := by
  have hx' : -x ≠ 0 := neg_ne_zero.mpr hx
  have h1 := Padic.norm_eq_zpow_neg_valuation hx
  have h2 := Padic.norm_eq_zpow_neg_valuation hx'
  rw [norm_neg] at h2
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  exact neg_injective ((zpow_right_strictMono₀ hp).injective (h2.symm.trans h1))


/-- The $n$-th level $E_n$ of the $p$-adic filtration is closed under addition:
if $P, Q \in E_n$ then $P + Q \in E_n$. -/
theorem PadicFiltrationMem.add_mem {W : WeierstrassCurve ℚ} [W.IsElliptic]
    (ha₁ : W.a₁ = 0) (ha₂ : W.a₂ = 0) (ha₃ : W.a₃ = 0)
    {p : ℕ} [Fact (Nat.Prime p)] {n : ℕ}
    {P Q : (W.baseChange ℚ_[p]).toAffine.Point}
    (hP : PadicFiltrationMem W p n P) (hQ : PadicFiltrationMem W p n Q) :
    PadicFiltrationMem W p n (P + Q) := by

  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    match P + Q with
    | .zero => trivial
    | .some _ _ _ => exact Or.inl rfl
  ·
    match P, Q with
    | .zero, _ =>

      exact hQ
    | _, .zero =>

      convert hP using 1
      exact add_zero _
    | .some x₁ y₁ h₁, .some x₂ y₂ h₂ =>


      simp only [PadicFiltrationMem] at hP hQ
      have hP' : y₁ ≠ 0 ∧ (n : ℤ) ≤ Padic.valuation x₁ - Padic.valuation y₁ := by
        rcases hP with rfl | h
        · omega
        · exact h
      have hQ' : y₂ ≠ 0 ∧ (n : ℤ) ≤ Padic.valuation x₂ - Padic.valuation y₂ := by
        rcases hQ with rfl | h
        · omega
        · exact h

      by_cases hxy : x₁ = x₂ ∧ y₁ = (W.baseChange ℚ_[p]).toAffine.negY x₂ y₂
      ·
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.1 hxy.2]
        trivial
      ·
        rw [WeierstrassCurve.Affine.Point.add_some hxy]
        simp only [PadicFiltrationMem]
        right


        exact PadicElliptic.addition_formula_preserves_valuation W ha₁ ha₂ ha₃ n h₁ h₂ hxy hP' hQ'

/-- The $n$-th level $E_n$ of the $p$-adic filtration is closed under negation:
if $P \in E_n$ then $-P \in E_n$. -/
theorem PadicFiltrationMem.neg_mem {W : WeierstrassCurve ℚ} [W.IsElliptic]
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    {p : ℕ} [Fact (Nat.Prime p)] {n : ℕ}
    {P : (W.baseChange ℚ_[p]).toAffine.Point}
    (hP : PadicFiltrationMem W p n P) :
    PadicFiltrationMem W p n (-P) := by
  match P with
  | .zero => trivial
  | .some x y hxy =>
    show n = 0 ∨ ((W.baseChange ℚ_[p]).toAffine.negY x y ≠ 0 ∧
      (n : ℤ) ≤ Padic.valuation x - Padic.valuation ((W.baseChange ℚ_[p]).toAffine.negY x y))
    have ha₁' : (W.baseChange ℚ_[p]).toAffine.a₁ = 0 := by
      simp [WeierstrassCurve.toAffine, WeierstrassCurve.baseChange, ha₁]
    have ha₃' : (W.baseChange ℚ_[p]).toAffine.a₃ = 0 := by
      simp [WeierstrassCurve.toAffine, WeierstrassCurve.baseChange, ha₃]
    have hneq : (W.baseChange ℚ_[p]).toAffine.negY x y = -y := by
      simp only [WeierstrassCurve.Affine.negY, ha₁', ha₃', zero_mul, sub_zero]
    rw [hneq]
    simp only [PadicFiltrationMem] at hP
    rcases hP with rfl | ⟨hy, hv⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨neg_ne_zero.mpr hy, by rw [padic_valuation_neg y hy]; exact hv⟩

/-- The $n$-th level $E_n$ of the $p$-adic filtration, packaged as an additive
subgroup of $E(\mathbb{Q}_p)$. -/
def padicFiltrationGroup (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (ha₁ : W.a₁ = 0) (ha₂ : W.a₂ = 0) (ha₃ : W.a₃ = 0)
    (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
    AddSubgroup (W.baseChange ℚ_[p]).toAffine.Point where
  carrier := {P | PadicFiltrationMem W p n P}
  zero_mem' := PadicFiltrationMem.zero W p n
  add_mem' ha hb := PadicFiltrationMem.add_mem ha₁ ha₂ ha₃ ha hb
  neg_mem' ha := PadicFiltrationMem.neg_mem ha₁ ha₃ ha

/-- Predicate: an affine point $P = (x, y) \in E(\mathbb{Q}_p)$ has
$p$-adically integral coordinates, i.e. $v_p(x) \geq 0$ and $v_p(y) \geq 0$
(the point at infinity is vacuously integral). -/
def CoordinatesPadicIntegral {W : WeierstrassCurve ℚ} [W.IsElliptic]
    {p : ℕ} [Fact (Nat.Prime p)]
    (P : (W.baseChange ℚ_[p]).toAffine.Point) : Prop :=
  match P with
  | .zero => True
  | .some x y _ => 0 ≤ Padic.valuation x ∧ 0 ≤ Padic.valuation y
