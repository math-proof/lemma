/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TateShafarevich.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ArithmeticGeometry.code.WeilChatelet.Part2
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.WeilChatelet
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.GaloisCohomology
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.WCGroupH1
import Abbrev.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology.Part3
import Def.v1.Atlas.ArithmeticGeometry.code.WCGroupH1


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

end
