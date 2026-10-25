/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.TateShafarevich.Part2
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.TateShafarevich
import Theorem.v1.Atlas.ArithmeticGeometry.code.JInvariant


noncomputable section

universe u

open WeierstrassCurve

namespace shortWeierstrassCurve

variable {R : Type*} [CommRing R] (a₄ a₆ : R)

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

end shortWeierstrassCurve
end
