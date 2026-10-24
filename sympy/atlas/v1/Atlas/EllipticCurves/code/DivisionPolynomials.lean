/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.FieldTheory.SeparableDegree
import sympy.atlas.v1.Atlas.EllipticCurves.code.IsogenyKernels
import Lemma.Complex.Atlas.v1.EllipticCurves.code.IsogenyKernels
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Isogenies
import Lemma.Complex.Atlas.v1.EllipticCurves.code.TorsionEndomorphism
import sympy.atlas.v1.Atlas.EllipticCurves.code.Isogenies
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Lemma53
import sympy.atlas.v1.Atlas.EllipticCurves.code.TorsionEndomorphism

open Polynomial
open scoped Polynomial.Bivariate

/-- A short Weierstrass curve $y^2 = x^3 + A x + B$ over a commutative ring $R$, parameterised
by the coefficients $A$ and $B$. -/
structure ShortWeierstrassCurve (R : Type*) where
  A : R
  B : R

namespace ShortWeierstrassCurve

variable {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R)

/-- The underlying Mathlib `WeierstrassCurve` of a short Weierstrass curve, with
$a_1 = a_2 = a_3 = 0$, $a_4 = A$, $a_6 = B$. -/
noncomputable def toWeierstrassCurve : WeierstrassCurve R :=
  ⟨0, 0, 0, E.A, E.B⟩

/-- The first Weierstrass coefficient $a_1$ of a short Weierstrass curve vanishes. -/
@[simp] lemma toWeierstrassCurve_a₁ : E.toWeierstrassCurve.a₁ = 0 := rfl
/-- The second Weierstrass coefficient $a_2$ of a short Weierstrass curve vanishes. -/
@[simp] lemma toWeierstrassCurve_a₂ : E.toWeierstrassCurve.a₂ = 0 := rfl
/-- The third Weierstrass coefficient $a_3$ of a short Weierstrass curve vanishes. -/
@[simp] lemma toWeierstrassCurve_a₃ : E.toWeierstrassCurve.a₃ = 0 := rfl
/-- The fourth Weierstrass coefficient $a_4$ of a short Weierstrass curve equals $A$. -/
@[simp] lemma toWeierstrassCurve_a₄ : E.toWeierstrassCurve.a₄ = E.A := rfl
/-- The sixth Weierstrass coefficient $a_6$ of a short Weierstrass curve equals $B$. -/
@[simp] lemma toWeierstrassCurve_a₆ : E.toWeierstrassCurve.a₆ = E.B := rfl

/-- The auxiliary invariant $b_2 = a_1^2 + 4 a_2$ of a short Weierstrass curve vanishes. -/
@[simp] lemma b₂_eq : E.toWeierstrassCurve.b₂ = 0 := by
  simp [WeierstrassCurve.b₂, toWeierstrassCurve]

/-- The auxiliary invariant $b_4 = 2 a_4 + a_1 a_3$ of a short Weierstrass curve equals $2A$. -/
@[simp] lemma b₄_eq : E.toWeierstrassCurve.b₄ = 2 * E.A := by
  simp [WeierstrassCurve.b₄, toWeierstrassCurve]

/-- The auxiliary invariant $b_6 = a_3^2 + 4 a_6$ of a short Weierstrass curve equals $4B$. -/
@[simp] lemma b₆_eq : E.toWeierstrassCurve.b₆ = 4 * E.B := by
  simp [WeierstrassCurve.b₆, toWeierstrassCurve]

/-- The auxiliary invariant $b_8$ of a short Weierstrass curve equals $-A^2$. -/
@[simp] lemma b₈_eq : E.toWeierstrassCurve.b₈ = -(E.A ^ 2) := by
  simp [WeierstrassCurve.b₈, toWeierstrassCurve]

/-- The $n$-th division polynomial $\psi_n \in R[X][Y]$ of a short Weierstrass curve, as a
bivariate polynomial. Computed from Mathlib's `WeierstrassCurve.ψ`. -/
noncomputable def divisionPoly (n : ℤ) : R[X][Y] :=
  E.toWeierstrassCurve.ψ n

/-- The zeroth division polynomial vanishes, $\psi_0 = 0$. -/
@[simp] lemma divisionPoly_zero : E.divisionPoly 0 = 0 :=
  E.toWeierstrassCurve.ψ_zero

/-- The first division polynomial is $\psi_1 = 1$. -/
@[simp] lemma divisionPoly_one : E.divisionPoly 1 = 1 :=
  E.toWeierstrassCurve.ψ_one

/-- The second division polynomial is $\psi_2$, equal to the Mathlib helper `ψ₂`. -/
@[simp] lemma divisionPoly_two : E.divisionPoly 2 = E.toWeierstrassCurve.ψ₂ :=
  E.toWeierstrassCurve.ψ_two

/-- The $x$-coordinate numerator polynomial $\phi_n \in R[X][Y]$ used in the multiplication-by-$n$
map: $\phi_n = X \psi_n^2 - \psi_{n+1} \psi_{n-1}$. -/
noncomputable def phiPoly (n : ℤ) : R[X][Y] :=
  E.toWeierstrassCurve.φ n

/-- The numerator polynomial of $\omega_n$ (the $y$-coordinate piece of $[n]$), defined as
$\psi_{n+2}\psi_{n-1}^2 - \psi_{n-2}\psi_{n+1}^2$. -/
noncomputable def omegaPolyNumer (n : ℤ) : R[X][Y] :=
  E.divisionPoly (n + 2) * E.divisionPoly (n - 1) ^ 2 -
  E.divisionPoly (n - 2) * E.divisionPoly (n + 1) ^ 2

/-- Evaluate a bivariate polynomial $p \in S[X][Y]$ at a point $(x_0, y_0) \in S \times S$
by first specialising $Y \mapsto y_0$ then $X \mapsto x_0$. -/
def Polynomial.evalBivariate {S : Type*} [CommRing S]
    (p : Polynomial (Polynomial S)) (x₀ y₀ : S) : S :=
  (p.eval (Polynomial.C y₀)).eval x₀

namespace ShortWeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] (E : ShortWeierstrassCurve F)

/-- Numeric evaluation of $\psi_n$ at the affine point $(x_0, y_0)$. -/
def evalDivisionPoly (n : ℤ) (x₀ y₀ : F) : F :=
  (E.divisionPoly n).evalBivariate x₀ y₀

/-- Numeric evaluation of $\phi_n$ at the affine point $(x_0, y_0)$. -/
def evalPhiPoly (n : ℤ) (x₀ y₀ : F) : F :=
  (E.phiPoly n).evalBivariate x₀ y₀

/-- Numeric evaluation of the $\omega_n$-numerator polynomial at $(x_0, y_0)$. -/
def evalOmegaNumer (n : ℤ) (x₀ y₀ : F) : F :=
  (E.omegaPolyNumer n).evalBivariate x₀ y₀

/-- The $x$-coordinate of $[n] P$ for $P = (x_0, y_0)$, given by $\phi_n / \psi_n^2$. -/
def mulByN_x (n : ℤ) (x₀ y₀ : F) : F :=
  E.evalPhiPoly n x₀ y₀ / (E.evalDivisionPoly n x₀ y₀) ^ 2

/-- Numeric value of $\omega_n(P) = \omega_n^{\mathrm{num}}/(4y_0)$ at the affine point
$P = (x_0, y_0)$. -/
def evalOmega (n : ℤ) (x₀ y₀ : F) : F :=
  E.evalOmegaNumer n x₀ y₀ / (4 * y₀)

/-- The $y$-coordinate of $[n] P$ for $P = (x_0, y_0)$, given by $\omega_n / \psi_n^3$. -/
def mulByN_y (n : ℤ) (x₀ y₀ : F) : F :=
  E.evalOmega n x₀ y₀ / (E.evalDivisionPoly n x₀ y₀) ^ 3

omit [DecidableEq F] in
/-- Base case: $\psi_1$ evaluates to $1$ at any point. -/
@[simp] lemma evalDivisionPoly_one (x₀ y₀ : F) :
    E.evalDivisionPoly 1 x₀ y₀ = 1 := by
  simp [evalDivisionPoly, divisionPoly, Polynomial.evalBivariate]

omit [DecidableEq F] in
/-- Base case: $\phi_1(x_0, y_0) = x_0$. -/
@[simp] lemma evalPhiPoly_one (x₀ y₀ : F) :
    E.evalPhiPoly 1 x₀ y₀ = x₀ := by
  simp [evalPhiPoly, phiPoly, Polynomial.evalBivariate, eval_C, eval_X]

/-- Data for the degree-$2$ Vélu isogeny: a $2$-torsion $x$-coordinate $x_0$ satisfying
$x_0^3 + A x_0 + B = 0$. -/
structure VeluDeg2Data (E : ShortWeierstrassCurve k) where
  x₀ : k
  root_eq : x₀ ^ 3 + E.A * x₀ + E.B = 0

namespace VeluDeg2Data

variable {E : ShortWeierstrassCurve k} (d : VeluDeg2Data E)

/-- Vélu parameter $t = 3 x_0^2 + A$. -/
def t : k := 3 * d.x₀ ^ 2 + E.A

/-- Vélu parameter $w = x_0 t = x_0 (3 x_0^2 + A)$. -/
def w : k := d.x₀ * d.t

/-- Vélu image parameter $A' = A - 5 t$ for the codomain curve. -/
def A' : k := E.A - 5 * d.t

/-- Vélu image parameter $B' = B - 7 w$ for the codomain curve. -/
def B' : k := E.B - 7 * d.w

/-- The image curve $E' : y^2 = x^3 + A' x + B'$ of the Vélu degree-$2$ isogeny. -/
def imageCurve : ShortWeierstrassCurve k := ⟨d.A', d.B'⟩

/-- Numerator of the $x$-coordinate component $\phi_x(x) = x^2 - x_0 x + t$. -/
def phi_x_numer (x : k) : k := x ^ 2 - d.x₀ * x + d.t

/-- Denominator of the $x$-coordinate component $\phi_x$, namely $x - x_0$. -/
def phi_x_denom (x : k) : k := x - d.x₀

/-- Factor appearing in the $y$-coordinate numerator: $(x - x_0)^2 - t$. -/
def phi_y_numer_factor (x : k) : k := (x - d.x₀) ^ 2 - d.t

/-- Denominator of the $y$-coordinate component: $(x - x_0)^2$. -/
def phi_y_denom (x : k) : k := (x - d.x₀) ^ 2

section FieldTheorems

variable {F : Type*} [Field F] {E : ShortWeierstrassCurve F} (d : VeluDeg2Data E)

/-- Bundled kernel data for the Vélu degree-$2$ isogeny: the kernel point is on $E$, the
denominators vanish at it, are nonzero elsewhere, and the kernel has order $2$. -/
structure VeluDeg2Kernel (E : ShortWeierstrassCurve F) (d : VeluDeg2Data E) where
  kernel_point_on_E : (0 : F) ^ 2 = d.x₀ ^ 3 + E.A * d.x₀ + E.B
  kernel_point_maps_to_zero : d.phi_x_denom d.x₀ = 0
  nonkernel_welldefined : ∀ x : F, x ≠ d.x₀ → d.phi_x_denom x ≠ 0
  kernel_order : ({(d.x₀, (0 : F))} : Finset (F × F)).card + 1 = 2

/-- The Vélu degree-$2$ kernel data associated to a Vélu degree-$2$ datum. -/
def velu_deg2_kernel : VeluDeg2Kernel E d where
  kernel_point_on_E := d.velu_deg2_kernel_on_curve
  kernel_point_maps_to_zero := (d.velu_deg2_kernel_denom_vanish).1
  nonkernel_welldefined := fun x hx => d.velu_deg2_kernel_unique hx
  kernel_order := by simp [Finset.card_singleton]

/-- Bundled Vélu degree-$2$ isogeny: a standard-form separable degree-$2$ isogeny together with
its kernel datum. -/
structure VeluDeg2Isogeny (E : ShortWeierstrassCurve F) (d : VeluDeg2Data E) where
  phi_maps_points : ∀ (x y : F), y ^ 2 = x ^ 3 + E.A * x + E.B →
    ((x - d.x₀) ^ 2 - d.t) ^ 2 * y ^ 2 =
      (x - d.x₀) * ((x ^ 2 - d.x₀ * x + d.t) ^ 3 +
        d.A' * (x ^ 2 - d.x₀ * x + d.t) * (x - d.x₀) ^ 2 +
        d.B' * (x - d.x₀) ^ 3)
  degree_eq_two : max (Polynomial.X ^ 2 - Polynomial.C d.x₀ * Polynomial.X +
    Polynomial.C d.t : F[X]).natDegree (Polynomial.X - Polynomial.C d.x₀ : F[X]).natDegree = 2
  is_separable : Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C d.x₀ *
    Polynomial.X + Polynomial.C d.t : F[X]) * (Polynomial.X - Polynomial.C d.x₀) -
    (Polynomial.X ^ 2 - Polynomial.C d.x₀ * Polynomial.X + Polynomial.C d.t) *
    Polynomial.derivative (Polynomial.X - Polynomial.C d.x₀) ≠ 0
  kernel : VeluDeg2Kernel E d

/-- The Vélu degree-$2$ isogeny constructed from a Vélu datum. -/
def velu_deg2_isogeny : VeluDeg2Isogeny E d where
  phi_maps_points := fun x y hcurve => d.velu_phi_maps_points hcurve
  degree_eq_two := d.velu_deg2_degree_eq_two
  is_separable := d.velu_deg2_is_separable
  kernel := d.velu_deg2_kernel

end FieldTheorems

end VeluDeg2Data

section VeluOdd

variable {k : Type*} [Field k]

/-- An affine point on a short Weierstrass curve: a pair $(x, y)$ together with a proof that
$y^2 = x^3 + A x + B$. -/
structure AffinePoint (E : ShortWeierstrassCurve k) where
  x : k
  y : k
  on_curve : y ^ 2 = x ^ 3 + E.A * x + E.B

variable {E : ShortWeierstrassCurve k}

/-- Vélu parameter $t_Q = 3 x_Q^2 + A$ associated with an affine point $Q$. -/
def AffinePoint.tQ (Q : AffinePoint E) : k := 3 * Q.x ^ 2 + E.A

/-- Vélu parameter $u_Q = 2 y_Q^2$ associated with an affine point $Q$. -/
def AffinePoint.uQ (Q : AffinePoint E) : k := 2 * Q.y ^ 2

/-- Vélu parameter $w_Q = u_Q + t_Q x_Q$ associated with an affine point $Q$. -/
def AffinePoint.wQ (Q : AffinePoint E) : k := Q.uQ + Q.tQ * Q.x

/-- Unfolds $t_Q$ to its defining formula. -/
@[simp] lemma AffinePoint.tQ_val (Q : AffinePoint E) :
    Q.tQ = 3 * Q.x ^ 2 + E.A := rfl

/-- Unfolds $u_Q$ to its defining formula. -/
@[simp] lemma AffinePoint.uQ_val (Q : AffinePoint E) :
    Q.uQ = 2 * Q.y ^ 2 := rfl

/-- Unfolds $w_Q$ to its defining formula $u_Q + t_Q x_Q$. -/
@[simp] lemma AffinePoint.wQ_val (Q : AffinePoint E) :
    Q.wQ = Q.uQ + Q.tQ * Q.x := rfl

/-- Data for the odd-degree Vélu isogeny: a finite set of nonidentity affine points such that
the kernel order $|S| + 1$ is odd. -/
structure VeluOddData (E : ShortWeierstrassCurve k) where
  pts : Finset (AffinePoint E)
  odd_order : Odd (pts.card + 1)

namespace VeluOddData

variable (d : VeluOddData E)

/-- Vélu sum $t = \sum_Q t_Q$ over the kernel points. -/
def t : k := d.pts.sum (fun Q => Q.tQ)

/-- Vélu sum $w = \sum_Q w_Q$ over the kernel points. -/
def w : k := d.pts.sum (fun Q => Q.wQ)

/-- Vélu image coefficient $A' = A - 5 t$. -/
def A' : k := E.A - 5 * d.t

/-- Vélu image coefficient $B' = B - 7 w$. -/
def B' : k := E.B - 7 * d.w

/-- The image curve $E' : y^2 = x^3 + A' x + B'$ of the odd-degree Vélu isogeny. -/
def imageCurve : ShortWeierstrassCurve k := ⟨d.A', d.B'⟩

/-- Unfolding the $A$-coefficient of the image curve. -/
@[simp] lemma imageCurve_A : d.imageCurve.A = d.A' := rfl
/-- Unfolding the $B$-coefficient of the image curve. -/
@[simp] lemma imageCurve_B : d.imageCurve.B = d.B' := rfl

/-- The rational function $r(x) = x + \sum_Q \left(\tfrac{t_Q}{x - x_Q} + \tfrac{u_Q}{(x - x_Q)^2}\right)$
defining the $x$-coordinate component of the Vélu isogeny. -/
noncomputable def r (x : k) : k :=
  x + d.pts.sum (fun Q => Q.tQ / (x - Q.x) + Q.uQ / (x - Q.x) ^ 2)

/-- The derivative $r'(x) = 1 - \sum_Q \left(\tfrac{t_Q}{(x - x_Q)^2} + \tfrac{2 u_Q}{(x - x_Q)^3}\right)$
used in the $y$-coordinate component. -/
noncomputable def r' (x : k) : k :=
  1 + d.pts.sum (fun Q => -(Q.tQ / (x - Q.x) ^ 2) - 2 * Q.uQ / (x - Q.x) ^ 3)

/-- The Vélu odd-degree map sends an on-curve point not in the kernel to a point on the
image curve. -/
end VeluOddData

end VeluOdd

end ShortWeierstrassCurve

open Polynomial

/-- An isogeny $\alpha$ over a field of characteristic $p$ has a Frobenius factorisation if it
factors as $\mathrm{Frob}^n \circ \alpha_{\mathrm{sep}}$ for a separable $\alpha_{\mathrm{sep}}$. -/
def IsogenyStandardForm.HasFrobeniusFactorization {F : Type*} [Field F]
    {p : ℕ} [CharP F p] (α : IsogenyStandardForm F) : Prop :=
  ∃ (α_sep : IsogenyStandardForm F) (n : ℕ),
    α_sep.IsSeparable ∧
    α.u = Polynomial.expand F (p ^ n) α_sep.u ∧
    α.v = Polynomial.expand F (p ^ n) α_sep.v ∧
    α.degree = p ^ n * α_sep.degree

namespace IsogenyStandardForm

/-- The multiplication-by-$n$ map packaged as an `IsogenyStandardForm`: numerator $\Phi_n$,
denominator $\Psi_n^2$, on the elliptic short Weierstrass curve. -/
noncomputable def mulByNStandardForm [E.toWeierstrassCurve.IsElliptic] {n : ℤ} (hn : (n : k) ≠ 0) :
    IsogenyStandardForm k where
  u := E.toWeierstrassCurve.Φ n
  v := E.toWeierstrassCurve.ΨSq n
  s := 1
  t := 1
  v_ne_zero := E.toWeierstrassCurve.ΨSq_ne_zero hn
  t_ne_zero := one_ne_zero
  coprime_uv := E.Phi_ΨSq_isCoprime n
  coprime_st := isCoprime_one_right

/-- An isogeny $\alpha$ has separable degree $d$ if it factors as
$\mathrm{Frob}^n \circ \alpha_{\mathrm{sep}}$ with $\deg \alpha_{\mathrm{sep}} = d$. -/
def HasSeparableDegree {p : ℕ} (_hp : Nat.Prime p) [CharP F p]
    (α : IsogenyStandardForm F) (d : ℕ) : Prop :=
  ∃ (α_sep : IsogenyStandardForm F) (n : ℕ),
    α_sep.IsSeparable ∧
    α.u = Polynomial.expand F (p ^ n) α_sep.u ∧
    α.v = Polynomial.expand F (p ^ n) α_sep.v ∧
    α_sep.degree = d

/-- An isogeny $\alpha$ has inseparable degree $d = p^n$ if its Frobenius factorisation has
exponent $n$. -/
def HasInseparableDegree {p : ℕ} (_hp : Nat.Prime p) [CharP F p]
    (α : IsogenyStandardForm F) (d : ℕ) : Prop :=
  ∃ (α_sep : IsogenyStandardForm F) (n : ℕ),
    α_sep.IsSeparable ∧
    α.u = Polynomial.expand F (p ^ n) α_sep.u ∧
    α.v = Polynomial.expand F (p ^ n) α_sep.v ∧
    d = p ^ n

/-- An isogeny is purely inseparable if its separable degree is $1$. -/
def IsPurelyInseparable' {p : ℕ} (hp : Nat.Prime p) [CharP F p]
    (α : IsogenyStandardForm F) : Prop :=
  α.HasSeparableDegree hp 1

/-- The separable degree of a standard-form isogeny: the maximum of the separable degrees of
its numerator and denominator. -/
noncomputable def separableDegree (α : IsogenyStandardForm F) : ℕ :=
  max α.u.natSepDegree α.v.natSepDegree

/-- The inseparable degree of a standard-form isogeny: total degree divided by separable
degree. -/
noncomputable def inseparableDegree (α : IsogenyStandardForm F) : ℕ :=
  α.degree / α.separableDegree

/-- An isogeny is purely inseparable if its separable degree equals $1$. -/
def IsPurelyInseparable (α : IsogenyStandardForm F) : Prop :=
  α.separableDegree = 1

/-- The size of the kernel of $\alpha$, computed as $\max(\mathrm{natSepDegree}(u),
\mathrm{natSepDegree}(v))$. -/
noncomputable def kernelSize {F : Type*} [Field F]
    (α : IsogenyStandardForm F) : ℕ := max α.u.natSepDegree α.v.natSepDegree

/-- The size of the kernel of $\alpha$ as an abstract group; this agrees with
`kernelSize` (cf. `groupKernelSize_eq_separableDegree`). -/
end IsogenyStandardForm

/-- The rational function $u/v \in K(F[X])$ representing the $x$-coordinate of a standard-form
isogeny in the fraction field. -/
noncomputable def xCoordRatFun (α : IsogenyStandardForm F) : FractionRing (Polynomial F) :=
  IsLocalization.mk' _ α.u ⟨α.v, mem_nonZeroDivisors_of_ne_zero α.v_ne_zero⟩

/-- Evaluate a polynomial $p \in F[X]$ at a rational function $r \in K$ by substitution. -/
noncomputable def evalAtRatFun (p : Polynomial F) (r : FractionRing (Polynomial F)) :
    FractionRing (Polynomial F) :=
  Polynomial.eval₂ (algebraMap _ (FractionRing (Polynomial F))) r p

/-- The composition of two $x$-coordinate rational functions $\beta \circ \gamma$ in the
fraction field. -/
noncomputable def compXCoord (β γ : IsogenyStandardForm F) : FractionRing (Polynomial F) :=
  evalAtRatFun β.u γ.xCoordRatFun / evalAtRatFun β.v γ.xCoordRatFun

/-- $\alpha = \beta \circ \gamma$ as rational $x$-coordinate maps: the $x$-coordinate rational
function of $\alpha$ equals the composition of those of $\beta$ and $\gamma$. -/
def IsCompOf (α β γ : IsogenyStandardForm F) : Prop :=
  α.xCoordRatFun = compXCoord β γ

/-- Auxiliary statement for prime-degree factorisation: any divisor $d$ of $\alpha$.degree
admits a length-$2$ decomposition with degrees $p$ and $d/p$. -/
inductive IsogenyChain {F : Type*} [Field F] [DecidableEq F] :
    WeierstrassCurve.Affine F → WeierstrassCurve.Affine F → Type _ where
  | single {E₁ E₂ : WeierstrassCurve.Affine F} (φ : Isogeny E₁ E₂) :
      IsogenyChain E₁ E₂
  | cons {E₁ E₂ E₃ : WeierstrassCurve.Affine F} (φ : Isogeny E₁ E₂)
      (rest : IsogenyChain E₂ E₃) : IsogenyChain E₁ E₃

open WeierstrassCurve.Affine in
/-- The compose of an `IsogenyChain` as an additive group homomorphism on point groups. -/
def IsogenyChain.compose {F : Type*} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F} :
    IsogenyChain E₁ E₂ → (E₁.Point →+ E₂.Point)
  | .single φ => φ.toAddMonoidHom
  | .cons φ rest => rest.compose.comp φ.toAddMonoidHom

open WeierstrassCurve.Affine in
/-- Predicate asserting that every link in an `IsogenyChain` has prime degree. -/
def IsogenyChain.allPrimeDegree {F : Type*} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F} :
    IsogenyChain E₁ E₂ → Prop
  | .single φ => Nat.Prime φ.degree
  | .cons φ rest => Nat.Prime φ.degree ∧ rest.allPrimeDegree

/-- Public alias for the $n$-th division polynomial of a short Weierstrass curve. -/
noncomputable def psi {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R) (n : ℤ) :
    R[X][Y] :=
  E.divisionPoly n

/-- Public alias for the $n$-th $\phi$-polynomial of a short Weierstrass curve. -/
noncomputable def phi {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R) (n : ℤ) :
    R[X][Y] :=
  E.phiPoly n

/-- Public alias for the numerator of the $n$-th $\omega$-polynomial. -/
noncomputable def omegaNumer {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R) (n : ℤ) :
    R[X][Y] :=
  E.omegaPolyNumer n

section BaseCases

variable {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R)

/-- Numerical evaluation of $\psi_n$ at the affine point $(x_0, y_0)$. -/
def evalPsi (n : ℤ) (x₀ y₀ : F) : F := E.evalDivisionPoly n x₀ y₀

/-- Numerical evaluation of $\phi_n$ at the affine point $(x_0, y_0)$. -/
def evalPhi (n : ℤ) (x₀ y₀ : F) : F := E.evalPhiPoly n x₀ y₀

/-- Numerical evaluation of $\omega_n$ at the affine point $(x_0, y_0)$. -/
def evalOmega (n : ℤ) (x₀ y₀ : F) : F := E.evalOmega n x₀ y₀

/-- $x$-coordinate of $[n] P$ for $P = (x_0, y_0)$, as $\phi_n(P) / \psi_n(P)^2$. -/
def mulByN_x (n : ℤ) (x₀ y₀ : F) : F := E.mulByN_x n x₀ y₀

/-- $y$-coordinate of $[n] P$ for $P = (x_0, y_0)$, as $\omega_n(P) / \psi_n(P)^3$. -/
def mulByN_y (n : ℤ) (x₀ y₀ : F) : F := E.mulByN_y n x₀ y₀
