/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TateShafarevich.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.WeilChatelet
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.WeilChatelet
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.GaloisCohomology
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.WCGroupH1
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.WCGroupH1

noncomputable section

universe u

open NumberField GaloisCohomology

/-- An elliptic curve over a field $k$: a Weierstrass curve together with the (instance)
witness that it is elliptic, i.e. that its discriminant is invertible. -/
structure EllipticCurveOver (k : Type u) [Field k] where
  curve : WeierstrassCurve k
  [isElliptic : curve.IsElliptic]

/-- A genus-one curve over $k$ together with its Jacobian (an elliptic curve over $k$) and a
chosen Weierstrass model over the algebraic closure. -/
structure GenusOneCurve (k : Type u) [Field k] where
  Jacobian : EllipticCurveOver k
  weierstrassModel :
    (Jacobian.curve.baseChange (AlgebraicClosure k)).toAffine.Point →
    WeierstrassCurve.VariableChange (AlgebraicClosure k)

/-- A *place* of a number field $k$ is either an infinite place (an archimedean valuation) or a
finite place (a nonarchimedean valuation), packaged as a sum type. -/
def NumberFieldPlace (k : Type u) [Field k] [NumberField k] : Type u :=
  NumberField.InfinitePlace k ⊕ NumberField.FinitePlace k

/-- Inject an infinite place into the disjoint union `NumberFieldPlace k`. -/
def NumberFieldPlace.infinite {k : Type u} [Field k] [NumberField k]
    (v : NumberField.InfinitePlace k) : NumberFieldPlace k :=
  Sum.inl v

/-- Inject a finite place into the disjoint union `NumberFieldPlace k`. -/
def NumberFieldPlace.finite {k : Type u} [Field k] [NumberField k]
    (v : NumberField.FinitePlace k) : NumberFieldPlace k :=
  Sum.inr v

/-- The Weil-Châtelet group $\mathrm{WC}(E/k)$ of an elliptic curve $E/k$: the set of
$E$-torsors modulo $k$-isomorphism. -/
abbrev WeilChateletGroup {k : Type u} [Field k] (E : EllipticCurveOver k) : Type (u + 1) :=
  haveI := E.isElliptic
  WC k E.curve (ECurvePointsAlgClosure k E.curve)

/-- The transported additive commutative group structure on the Weil-Châtelet group, coming from
its bijection with the first Galois cohomology group $H^1$. -/
noncomputable instance instAddCommGroupWeilChateletGroup {k : Type u} [Field k]
    (E : EllipticCurveOver k) : AddCommGroup (WeilChateletGroup E) :=
  haveI := E.isElliptic
  WC.addCommGroupOfData (WCH1Data.mk' k E.curve (ECurvePointsAlgClosure k E.curve)
    (AbsGaloisGroup k))

/-- The first Galois cohomology group
$H^1(\mathrm{Gal}(\bar k/k), E(\bar k))$ realising the Weil-Châtelet group of $E/k$. -/
abbrev GaloisCohomologyH1 (k : Type u) [Field k] (E : EllipticCurveOver k) : Type u :=
  WeilChateletGroupReal k E.curve

/-- The Galois cohomology group inherits its additive commutative group structure from the
underlying $H^1$ construction. -/
instance GaloisCohomologyH1.instAddCommGroup (k : Type u) [Field k]
    (E : EllipticCurveOver k) : AddCommGroup (GaloisCohomologyH1 k E) :=
  inferInstance

/-- The isomorphism between the Weil-Châtelet group of $E/k$ (torsors mod $k$-isomorphism) and
the first Galois cohomology group $H^1(\mathrm{Gal}(\bar k/k), E(\bar k))$. -/
noncomputable def WeilChatelet_iso_H1 {k : Type u} [Field k] (E : EllipticCurveOver k) :
    WeilChateletGroup E ≃+ GaloisCohomologyH1 k E :=
  haveI := E.isElliptic
  wc_h1_equiv (WCH1Data.mk' k E.curve (ECurvePointsAlgClosure k E.curve)
    (AbsGaloisGroup k))


/-- The class in the Weil-Châtelet group $\mathrm{WC}(\mathrm{Jac}(C)/k)$ associated to a
genus-one curve $C$ over $k$. -/
end
