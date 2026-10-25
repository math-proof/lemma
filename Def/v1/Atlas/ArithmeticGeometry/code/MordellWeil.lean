/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/MordellWeil.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite


namespace WeakMordellWeil

open scoped Classical

/-- Affine equation of the elliptic curve $E : y^2 = x(x^2 + ax + b)$, used
in the descent step of the Mordell-Weil theorem (Chapter 25). -/
def onCurveE (a b x y : ℚ) : Prop :=
  y ^ 2 = x * (x ^ 2 + a * x + b)

/-- Affine equation of the 2-isogenous curve
$E' : Y^2 = X(X^2 - 2aX + (a^2 - 4b))$ used as the target of the 2-isogeny
$\varphi : E \to E'$. -/
def onCurveE' (a b X Y : ℚ) : Prop :=
  Y ^ 2 = X * (X ^ 2 + (-2 * a) * X + (a ^ 2 - 4 * b))

/-- A point $(X, Y) \in E'(\mathbb{Q})$ lies in the image of the 2-isogeny
$\varphi : E \to E'$ if there exists $(x, y) \in E(\mathbb{Q})$ with $x \neq 0$,
$X = x + a + b/x$ and $Y = y(1 - b/x^2)$. -/
def inImageOfPhi (a b X Y : ℚ) : Prop :=
  ∃ x y : ℚ, onCurveE a b x y ∧ x ≠ 0 ∧
    X = x + a + b / x ∧ Y = y * (1 - b / x ^ 2)


/-- Membership predicate $X \in \mathbb{Q}^{\times 2}$: the rational $X$ is
nonzero and a square. -/
def mem_QxSq (X : ℚ) : Prop :=
  X ≠ 0 ∧ IsSquare X

end WeakMordellWeil
