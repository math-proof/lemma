/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Twists.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.JInvariant
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.JInvariant

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ArithmeticGeometry

/-- The affine scheme $\mathrm{Spec}\, R$ for a commutative ring $R$. -/
noncomputable abbrev specOf (R : Type u) [CommRing R] : Scheme.{u} := Spec (.of R)

variable (k : Type u) [Field k]

/-- The morphism of schemes $\mathrm{Spec}\, \overline{k} \to \mathrm{Spec}\, k$
induced by the algebraic closure inclusion $k \hookrightarrow \overline{k}$. -/
noncomputable def specAlgClosureToSpec :
    specOf (AlgebraicClosure k) ⟶ specOf k :=
  Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))

/-- Base change of a $k$-scheme $X$ along the algebraic closure, producing the
$\overline{k}$-scheme $X_{\overline{k}} := X \times_{\mathrm{Spec}\, k} \mathrm{Spec}\, \overline{k}$. -/
noncomputable def baseChangeToAlgClosure (X : Scheme.{u}) [X.Over (specOf k)] : Scheme.{u} :=
  pullback (X ↘ specOf k) (specAlgClosureToSpec k)

/-- The base change $X_{\overline{k}}$ is canonically a scheme over
$\mathrm{Spec}\, \overline{k}$. -/
noncomputable instance baseChangeToAlgClosure_over (X : Scheme.{u}) [X.Over (specOf k)] :
    (baseChangeToAlgClosure k X).Over (specOf (AlgebraicClosure k)) :=
  Scheme.canonicallyOverPullback.toOverClass

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

/-- The ring homomorphism $\mathrm{ULift}\, \mathbb{Q} \to \mathbb{Q}$ coming
from the canonical equivalence. A universe-polymorphism utility. -/
noncomputable abbrev uliftQToQ : ULift.{v, 0} ℚ →+* ℚ :=
  (ULift.ringEquiv (R := ℚ)).toRingHom


end GenusOneTwist
