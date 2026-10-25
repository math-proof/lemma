/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Twists.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Def.v1.Atlas.ArithmeticGeometry.code.JInvariant.Part3
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.JInvariant
import Instance.v1.Atlas.ArithmeticGeometry.code.Twists
open AlgebraicGeometry CategoryTheory Limits

universe u


namespace ArithmeticGeometry

variable (k : Type u) [Field k]

/-- **Definition 26.1.** Two $k$-schemes $X$ and $Y$ are *twists* of each other
if they become isomorphic over the algebraic closure: $X_{\overline{k}} \cong
Y_{\overline{k}}$ as $\overline{k}$-schemes. -/
def AreTwists (X Y : Scheme.{u}) [X.Over (specOf k)] [Y.Over (specOf k)] : Prop :=
  Nonempty (
    Scheme.asOver (baseChangeToAlgClosure k X) (specOf (AlgebraicClosure k)) ≅
    Scheme.asOver (baseChangeToAlgClosure k Y) (specOf (AlgebraicClosure k)))

variable {k}

/-- A genus-one curve $C$ is a *twist* of an elliptic curve $E$ if its Jacobian
becomes isomorphic to $E$ over the algebraic closure $\overline{k}$, via a
Weierstrass variable change. -/
def GenusOneCurve.IsTwistOfEllipticCurve {k : Type v} [Field k]
    (C : GenusOneCurve k) (E : EllipticCurveOver k) : Prop :=
  ∃ (σ : WeierstrassCurve.VariableChange (AlgebraicClosure k)),
    σ • (C.Jacobian.curve.baseChange (AlgebraicClosure k)) =
    E.curve.baseChange (AlgebraicClosure k)

/-- Two elliptic curves over $k$ are *isomorphic over $k$* if there exists a
Weierstrass variable change defined over $k$ taking one to the other. -/
def EllipticCurveOver.IsIsomorphicOverK {k : Type v} [Field k]
    (E₁ E₂ : EllipticCurveOver k) : Prop :=
  ∃ σ : WeierstrassCurve.VariableChange k, E₁.curve = σ • E₂.curve

end ArithmeticGeometry
