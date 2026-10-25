/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Squarefree.Basic
import Instance.v1.Atlas.EllipticCurves.code.Isogenies.Part4
open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace IsogenyStandardForm

variable {F : Type u} [Field F]

namespace WithCurveData

variable (α : WithCurveData F)

/-- Alternative definition of a rational map from `f₁ = 0` to `f₂ = 0`, as a
quotient of the type of `RationalMapTriple`s by the equivalence relation. -/
def RationalMapAlt {k : Type u} [CommRing k]
    (f₁ f₂ : MvPolynomial (Fin 3) k)
    [Fact ((Ideal.span ({f₁} : Set (MvPolynomial (Fin 3) k))).IsPrime)] : Type u :=
  Quotient (RationalMapTriple.setoid f₁ f₂)

/-- A rational-map triple `t` is *defined at* a point `P` if at least one of its
homogeneous components is nonzero on `P`. -/
def RationalMapTriple.IsDefinedAt {k : Type u} [CommRing k]
    {f₁ f₂ : MvPolynomial (Fin 3) k}
    (t : RationalMapTriple f₁ f₂) (P : Fin 3 → k) : Prop :=
  MvPolynomial.eval P t.ψ_x ≠ 0 ∨
  MvPolynomial.eval P t.ψ_y ≠ 0 ∨
  MvPolynomial.eval P t.ψ_z ≠ 0

end ProjectiveCurve

namespace EllipticCurve

variable {F : Type u} [Field F] [DecidableEq F]

variable (E : WeierstrassCurve.Affine F)

/-- An additive group endomorphism of `E(F)` is *algebraic* if it is either the
zero map or comes from some `Isogeny E E`. -/
def IsAlgebraicEndomorphism (φ : AddMonoid.End E.Point) : Prop :=
  φ = 0 ∨ ∃ (ι : Isogeny E E), ι.toAddMonoidHom = φ

/-- The endomorphism ring `End(E)` of `E`, defined as the subtype of additive
endomorphisms of `E.Point` which are algebraic. -/
def EndomorphismRing : Type u :=
  { φ : AddMonoid.End E.Point // IsAlgebraicEndomorphism E φ }

/-- An additive automorphism of `E.Point` is *algebraic* if it comes from a pair
of mutually-inverse isogenies. -/
def IsAlgebraicAutomorphism (f : AddAut E.Point) : Prop :=
  ∃ (φ : Isogeny E E) (ψ : Isogeny E E),
    (∀ P, ψ (φ P) = P) ∧ (∀ Q, φ (ψ Q) = Q) ∧ f.toAddMonoidHom = φ.toAddMonoidHom

/-- The automorphism group `Aut(E)` of `E`, the subtype of additive automorphisms
of `E.Point` arising from isogenies. -/
def AutomorphismGroup : Type u :=
  { f : AddAut E.Point // IsAlgebraicAutomorphism E f }

/-- Extract the underlying additive endomorphism from an element of
`EndomorphismRing E`. -/
def EndomorphismRing.val (φ : EndomorphismRing E) : AddMonoid.End E.Point := φ.1

variable {E}

/-- Every isogeny `E → E` is an algebraic endomorphism of `E.Point`. -/
def Isogeny.toEndomorphism (φ : Isogeny E E) : EndomorphismRing E :=
  ⟨φ.toAddMonoidHom, Or.inr ⟨φ, rfl⟩⟩

/-- The zero endomorphism in `EndomorphismRing E`. -/
def EndomorphismRing.zero : EndomorphismRing E :=
  ⟨0, Or.inl rfl⟩

/-- The identity endomorphism in `EndomorphismRing E`. -/
def EndomorphismRing.one : EndomorphismRing E :=
  Isogeny.toEndomorphism (Isogeny.id E)

/-- Apply an algebraic endomorphism to a point of `E`. -/
def EndomorphismRing.apply (α : EndomorphismRing E) (P : E.Point) : E.Point :=
  α.1 P

/-- The endomorphism ring `End(E)` of an elliptic curve is a (noncommutative)
ring; the proof requires geometric content and is left as `sorry`. -/

end EllipticCurve

namespace WeierstrassCurve.Affine

/-- A Weierstrass curve is in *short Weierstrass form* if `a₁ = a₂ = a₃ = 0`,
i.e. its equation is `y² = x³ + a₄ x + a₆`. -/
def IsShortWeierstrass {R : Type u} [CommRing R] (W : WeierstrassCurve.Affine R) : Prop :=
  W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0

end WeierstrassCurve.Affine
end IsogenyStandardForm
