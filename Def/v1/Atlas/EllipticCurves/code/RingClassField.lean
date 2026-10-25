/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/RingClassField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.EllipticCurves.code.PointCounting.Part2
import Lemma.Complex.Atlas.v1.EllipticCurves.code.PointCounting
import Lemma.Complex.Atlas.v1.EllipticCurves.code.OrdinarySupersingular
import Lemma.Complex.Atlas.v1.EllipticCurves.code.HilbertClassPolynomial
import Lemma.Complex.Atlas.v1.EllipticCurves.code.CMTorsor
import Def.v1.Atlas.EllipticCurves.code.OrdinarySupersingular
import Def.v1.Atlas.EllipticCurves.code.HilbertClassPolynomial.Part2
import Def.v1.Atlas.EllipticCurves.code.CMTorsor.Part7


namespace Elliptic_Curves

/-- An integer `D` is the discriminant of an imaginary quadratic order if it
is negative and congruent to `0` or `1` modulo `4`. -/
def IsImagQuadDiscriminant (D : ℤ) : Prop :=
  D < 0 ∧ (D % 4 = 0 ∨ D % 4 = 1)

/-- The ideal class group of the imaginary quadratic order of discriminant `D`,
abstractly defined as a type (concrete construction left unspecified). -/
def NormEquation (D : ℤ) (p : ℕ) (t v : ℤ) : Prop :=
  4 * (p : ℤ) = t ^ 2 - v ^ 2 * D

/-- The prime `p` satisfies the Cornacchia norm equation for discriminant `D`
if there exist integers `t, v` with `4p = t^2 - v^2 D` and `p ∤ t`. -/
def SatisfiesNormEquation (D : ℤ) (p : ℕ) : Prop :=
  ∃ t v : ℤ, NormEquation D p t v ∧ ¬((p : ℤ) ∣ t)

/-- The Hilbert class polynomial `H_D(X)` of discriminant `D` realized over
`ℤ` (`1` outside the imaginary quadratic discriminant range). -/
noncomputable def hilbertClassPolynomialZ (D : ℤ) : Polynomial ℤ := by
  classical
  exact if h : _root_.IsImaginaryQuadraticDiscriminant D then
    ((Polynomial.mem_lifts _).mp (_root_.hilbertClassPoly_int_coeffs D h)).choose
  else 1

/-- `p` is the norm of a principal ideal in the order of discriminant `D` iff
there exist integers `t, v` with `4p = t^2 - v^2 D` and `2 ∣ t - vD`. This is
condition (i) in Theorem 21.5 of Sutherland. -/
def IsNormOfPrincipalIdeal (D : ℤ) (p : ℕ) : Prop :=
  ∃ t v : ℤ, 4 * (p : ℤ) = t ^ 2 - v ^ 2 * D ∧ 2 ∣ (t - v * D)

/-- Condition (ii) of Theorem 21.5: the Legendre symbol `(D/p) = 1` and the
Hilbert class polynomial `H_D` splits into linear factors over `𝔽_p`. -/
def LegendreOneAndHDSplits (D : ℤ) (p : ℕ) : Prop :=
  jacobiSym D p = 1 ∧ ((hilbertClassPolynomialZ D).map (Int.castRingHom (ZMod p))).Splits

/-- Condition (iii) of Theorem 21.5: `p` splits completely in the ring class
field of discriminant `D`, expressed as: there is a number field `L` over
which `H_D` splits and all maximal ideals above `p` have absolute norm `p`. -/
def SplitsCompletelyInRCF (D : ℤ) (p : ℕ) : Prop :=
  ∃ (L : Type) (hF : Field L) (hNF : @NumberField L hF),
    letI := hF
    letI := hNF

    ((hilbertClassPolynomialZ D).map (algebraMap ℤ L)).Splits ∧

    (∀ (P : Ideal (NumberField.RingOfIntegers L)),
      P.IsMaximal →
      (p : NumberField.RingOfIntegers L) ∈ P →
      Ideal.absNorm P = p)

/-- Definition 21.4 (Sutherland): the Kronecker symbol `(D/p)`. For odd primes
it agrees with the Legendre symbol; for `p = 2` it is `0` if `2 ∣ D`, `+1`
if `D ≡ ±1 mod 8`, and `-1` if `D ≡ ±3 mod 8`. -/
noncomputable def kroneckerSymbol (p : ℕ) [hp : Fact (Nat.Prime p)] (D : ℤ) : ℤ :=
  if p = 2 then
    if D % 2 = 0 then 0
    else if D % 8 = 1 ∨ D % 8 = 7 then 1
    else -1
  else
    legendreSym p D

end Elliptic_Curves
