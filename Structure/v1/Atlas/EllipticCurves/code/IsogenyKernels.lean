/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyKernels.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.Tactic.LinearCombination
open Polynomial


/-- A *short Weierstrass curve* $y^2 = x^3 + A x + B$, recorded by its
coefficients $A, B \in k$. -/
structure ShortWeierstrassCurve (k : Type*) where
  A : k
  B : k

/-- An *affine point* $(x, y)$ on a short Weierstrass curve $E$, together with
a proof that it satisfies the curve equation $y^2 = x^3 + A x + B$. -/
structure AffinePoint (E : ShortWeierstrassCurve k) where
  x : k
  y : k
  on_curve : y ^ 2 = x ^ 3 + E.A * x + E.B

variable {E : ShortWeierstrassCurve k}

/-- Input data for the *Vélu degree-2* isogeny construction: a $k$-rational
$2$-torsion point $(x_0, 0)$ on $E$, encoded by $x_0$ together with a proof
that $x_0$ is a root of the cubic $x^3 + A x + B$. -/
structure VeluDeg2Data (E : ShortWeierstrassCurve k) where
  x₀ : k
  is_root : x₀ ^ 3 + E.A * x₀ + E.B = 0

