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
import Def.v1.Atlas.EllipticCurves.code.IsogenyKernels.Part4
import Lemma.Complex.Atlas.v1.EllipticCurves.code.IsogenyKernels
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Isogenies
import Lemma.Complex.Atlas.v1.EllipticCurves.code.TorsionEndomorphism
import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Lemma53
import Def.v1.Atlas.EllipticCurves.code.TorsionEndomorphism.Part3
import Theorem.v1.Atlas.EllipticCurves.code.DivisionPolynomials.Part5
open Polynomial
open scoped Polynomial.Bivariate


namespace ShortWeierstrassCurve

variable {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R)

namespace ShortWeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] (E : ShortWeierstrassCurve F)

section VeluOdd

variable {k : Type*} [Field k]

variable {E : ShortWeierstrassCurve k}

namespace VeluOddData

variable (d : VeluOddData E)

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

end ShortWeierstrassCurve
