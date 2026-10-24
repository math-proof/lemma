/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.TateShafarevich
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.TateShafarevich

noncomputable section

universe u

open WeierstrassCurve

/-- The Weierstrass curve in *short form* $y^2 = x^3 + a_4 x + a_6$, obtained by
setting $a_1 = a_2 = a_3 = 0$. -/
def shortWeierstrassCurve {R : Type*} [CommRing R] (a₄ a₆ : R) : WeierstrassCurve R :=
  ⟨0, 0, 0, a₄, a₆⟩

namespace shortWeierstrassCurve

variable {R : Type*} [CommRing R] (a₄ a₆ : R)

/-- **Definition 26.1.** The $j$-invariant of an elliptic curve $E$ over a field
$k$, extracted from its underlying Weierstrass curve. -/
def EllipticCurveOver.jInvariant {k : Type*} [Field k] (E : EllipticCurveOver k) : k :=
  @WeierstrassCurve.j _ _ E.curve E.isElliptic

/-- **Theorem 26.3 (surjectivity).** Over any field $k$, every value $j \in k$
arises as the $j$-invariant of some elliptic curve over $k$. -/
theorem j_invariant_surjective {k : Type*} [Field k] (j : k) :
    ∃ E : EllipticCurveOver k, E.jInvariant = j := by
  classical
  exact ⟨⟨WeierstrassCurve.ofJ j⟩, WeierstrassCurve.ofJ_j j⟩

/-- A choice of elliptic curve over $k$ whose $j$-invariant equals $j$, witnessing
the surjectivity of the $j$-invariant. -/
noncomputable def ellipticCurveOfJ {k : Type*} [Field k] (j : k) : EllipticCurveOver k :=
  (j_invariant_surjective j).choose

/-- The Jacobian of a genus-one curve $C$, viewed as an elliptic curve over $k$. -/
def GenusOneCurve.jacobian (C : GenusOneCurve k) : EllipticCurveOver k :=
  C.Jacobian

/-- The underlying type carrying $\mathrm{Pic}^0(C)$, the degree-zero Picard
group of a genus-one curve $C$ over $k$. -/
def EllipticCurveOver.RationalPoints (E : EllipticCurveOver k) :=
  E.curve.toAffine.Point

/-- The product $\prod_v \mathrm{WC}(E/k_v)$ of local Weil–Châtelet groups
over all places $v$ of the number field $k$. -/
def LocalWCProduct {k : Type u} [Field k] [NumberField k] (E : EllipticCurveOver k) : Type (u + 1) :=
  ∀ v : NumberFieldPlace k, WeilChateletGroupLocal E v

/-- The componentwise abelian group structure on `LocalWCProduct E`, inherited
from the pointwise product of local Weil–Châtelet groups. -/
def WeilChateletGroup.localizationMapAxiom {k : Type u} [Field k] [NumberField k]
    (E : EllipticCurveOver k) : WeilChateletGroup E →+ LocalWCProduct E :=
  AddMonoidHom.mk' (fun x => fun v => localizationMap E v x)
    (fun a b => funext (fun v => map_add (localizationMap E v) a b))

/-- The global-to-local restriction homomorphism on Weil–Châtelet groups, sending
$\xi \in \mathrm{WC}(E/k)$ to the tuple of its images $(\xi_v)_v$. -/
noncomputable def WeilChateletGroup.localizationMap (E : EllipticCurveOver k) :
    WeilChateletGroup E →+ LocalWCProduct E := WeilChateletGroup.localizationMapAxiom E

/-- The Tate–Shafarevich group $Ш(E/k)$ realised as a subgroup of
$\mathrm{WC}(E/k)$: the kernel of the localization map. -/
def TateShafarevich.asKernel (E : EllipticCurveOver k) :
    AddSubgroup (WeilChateletGroup E) :=
  (WeilChateletGroup.localizationMap E).ker

/-- The set of $\bar k$-rational points of the Jacobian of $C$, used as base
points for the elliptic-curve structure of $C \otimes_k \bar k$. -/
def GenusOneCurve.PointOverAlgClosure {k : Type u} [Field k]
    (C : GenusOneCurve k) : Type u :=
  (C.Jacobian.curve.baseChange (AlgebraicClosure k)).toAffine.Point

/-- Given a $\bar k$-point $O$ of $C$, the associated elliptic curve over
$\bar k$ obtained by translating the Weierstrass model so that $O$ becomes the
identity. -/
noncomputable def GenusOneCurve.ellipticCurveAtBasePoint {k : Type u} [Field k]
    (C : GenusOneCurve k) (O : C.PointOverAlgClosure) :
    EllipticCurveOver (AlgebraicClosure k) :=
  haveI : C.Jacobian.curve.IsElliptic := C.Jacobian.isElliptic
  { curve := (C.weierstrassModel O) • (C.Jacobian.curve.baseChange (AlgebraicClosure k)) }

/-- An elliptic curve bundles an `IsElliptic` instance on its underlying
Weierstrass curve, registered for typeclass search. -/
instance EllipticCurveOver.instIsElliptic {k : Type*} [Field k] (E : EllipticCurveOver k) :
    E.curve.IsElliptic := E.isElliptic

/-- The $j$-invariant $j(C) \in k$ of a genus-one curve $C$, defined as the
$j$-invariant of its Jacobian. -/
def GenusOneCurve.jInvariant {k : Type u} [Field k] (C : GenusOneCurve k) : k :=
  C.Jacobian.jInvariant
