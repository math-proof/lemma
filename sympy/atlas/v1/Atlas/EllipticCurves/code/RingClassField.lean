/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/RingClassField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import sympy.atlas.v1.Atlas.EllipticCurves.code.PointCounting
import Lemma.Complex.Atlas.v1.EllipticCurves.code.PointCounting
import Lemma.Complex.Atlas.v1.EllipticCurves.code.OrdinarySupersingular
import Lemma.Complex.Atlas.v1.EllipticCurves.code.HilbertClassPolynomial
import Lemma.Complex.Atlas.v1.EllipticCurves.code.CMTorsor
import sympy.atlas.v1.Atlas.EllipticCurves.code.OrdinarySupersingular
import sympy.atlas.v1.Atlas.EllipticCurves.code.HilbertClassPolynomial
import sympy.atlas.v1.Atlas.EllipticCurves.code.CMTorsor

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

/-- A "ring class field prime" for Theorem 21.12 (Deuring): a positive integer
`q > 1` that is coprime to the discriminant `D`, intended to represent a
prime power norm of a prime in the ring class field. -/
structure RingClassFieldPrime (D : ℤ) where
  q : ℕ
  q_pos : 1 < q
  coprime_q_D : Nat.Coprime q D.natAbs

/-- The Hilbert class polynomial of discriminant `D` viewed as a polynomial
over an arbitrary field `F`, obtained by base change from the integral form. -/
noncomputable def hilbertClassPolynomial (D : ℤ) (F : Type*) [Field F] : Polynomial F :=
  (Elliptic_Curves.hilbertClassPolynomialZ D).map (Int.castRingHom F)

/-- `Ell_𝒪(F)`: the set of `j`-invariants of elliptic curves over the finite
field `F` whose endomorphism ring is the order of discriminant `D`. -/
end Deuring

end Elliptic_Curves

open NumberField

noncomputable section

namespace DeuringLifting

/-- `IsReductionOfCurve E E_star 𝔮 e` is the predicate stating that the curve
`E_star` over the number field `L` has good reduction modulo the prime `𝔮`
identifying with `E` via the ring isomorphism `e : F ≃+* 𝒪_L/𝔮`. -/
opaque IsReductionOfCurve
    {F : Type} [Field F] [DecidableEq F] [Fintype F]
    {L : Type} [Field L] [DecidableEq L] [NumberField L]
    (E : WeierstrassCurve.Affine F)
    (E_star : WeierstrassCurve.Affine L)
    (𝔮 : Ideal (𝓞 L)) [𝔮.IsMaximal]
    (e : F ≃+* (𝓞 L ⧸ 𝔮)) : Prop

/-- `IsReductionOfEndomorphism` states that the endomorphism `φ_star` of the
lift `E_star` reduces to the endomorphism `φ` of `E` modulo `𝔮`, given that
`E_star` is a good reduction lift of `E`. -/
opaque IsReductionOfEndomorphism
    {F : Type} [Field F] [DecidableEq F] [Fintype F]
    {L : Type} [Field L] [DecidableEq L] [NumberField L]
    (E : WeierstrassCurve.Affine F)
    (E_star : WeierstrassCurve.Affine L)
    (φ : AddMonoid.End E.Point)
    (φ_star : AddMonoid.End E_star.Point)
    (𝔮 : Ideal (𝓞 L)) [𝔮.IsMaximal]
    (e : F ≃+* (𝓞 L ⧸ 𝔮))
    (hcurve : IsReductionOfCurve E E_star 𝔮 e) : Prop

/-- Theorem 21.13 (Deuring lifting theorem, Sutherland): every nonzero
endomorphism `φ` of an elliptic curve `E/𝔽_q` lifts to a characteristic-zero
endomorphism `φ_star` of an elliptic curve `E_star` over a number field `L`
with good reduction at a prime `𝔮` of residue field `𝔽_q`. -/
end DeuringLifting

namespace RingClassField

/-- Predicate (in `Prop`) form of "`D` is the discriminant of an imaginary
quadratic order": `D < 0` and `D ≡ 0` or `1 mod 4`. -/
structure IsImagQuadDisc (D : ℤ) : Prop where
  neg : D < 0
  cong : D % 4 = 0 ∨ D % 4 = 1

/-- The imaginary quadratic field `K = ℚ(√D)`, abstractly defined as a type. -/
class fixes a point. -/
end RingClassField

end

open Elliptic_Curves

namespace CMMethod

/-- Predicate saying that the elliptic curve `E/F` has prescribed
`j`-invariant `j₀ ∈ F`. -/
structure CMOutput (F : Type*) [Field F] [Fintype F] [DecidableEq F] where
  curve : WeierstrassCurve.Affine F
  trace : ℤ
  frob_trace_eq : Hasse.traceFrobenius curve = trace ∨
                  Hasse.traceFrobenius curve = -trace

end CMMethod

namespace ProperIdealNormCount

open Elliptic_Curves

/-- The conductor `[𝒪_K : 𝒪]` of the order of discriminant `D` in its
maximal order, as a natural number. -/
end ProperIdealNormCount

namespace RingClassFieldRamification

open Elliptic_Curves

/-- Predicate: the rational prime `p` is unramified in the ring class field
of discriminant `D`. -/
end RingClassFieldRamification

namespace ImagQuadPrimeSplitting

open Elliptic_Curves

/-- Roots in `ZMod p` of the minimal polynomial of `ω = (D + √D)/2` (or
`√D`) for the imaginary quadratic discriminant `D`. -/
noncomputable def rootsMinPolyMod (D : ℤ) (p : ℕ) [Fact (Nat.Prime p)] : Finset (ZMod p) :=
  if D % 4 = 1 then
    Finset.univ.filter (fun x : ZMod p => x ^ 2 - x + ((1 - D) / 4 : ℤ) = 0)
  else
    Finset.univ.filter (fun x : ZMod p => x ^ 2 + ((-D / 4 : ℤ) : ZMod p) = 0)

/-- The number of `𝒪_K`-ideals of norm `p`, counted by the roots of the
minimal polynomial of `ω` modulo `p`. -/
noncomputable def numIdealsOfNorm (D : ℤ) (p : ℕ) [Fact (Nat.Prime p)] : ℤ :=
  (rootsMinPolyMod D p).card

/-- The prime ideal `𝔭 = (p, ω - r)` in `ℤ[√d]` above a rational prime `p`
and a root `r` of `x² + d ≡ 0 mod p`, used in Lemma 21.6. -/
def primeIdealAbove (p : ℕ) (r : ℤ) : Ideal (ℤ√d) :=
  Ideal.span {(p : ℤ√d), (⟨-r, 1⟩ : ℤ√d)}

/-- Infrastructure form: in `ℤ[√d]` with `d < 0`, every prime ideal `𝔭 ≠ ⊥`
of norm `p` has the form `(p, ω - r)` for some `r` with `r² + d ≡ 0 mod p`. -/
end ImagQuadPrimeFactorization

namespace ImagQuadPrimeSplitting.IdealRootBijection

open Elliptic_Curves ImagQuadPrimeSplitting

/-- The ideal `(p, ω - r)` in `ℤ[√d]` is nonzero and has norm `p` whenever
`r² + d ≡ 0 mod p`. -/
end ImagQuadPrimeSplitting.IdealRootBijection

namespace CMMethod.TwistSelection

open Elliptic_Curves
