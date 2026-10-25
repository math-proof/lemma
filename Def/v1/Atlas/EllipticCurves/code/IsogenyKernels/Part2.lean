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
import Theorem.v1.Atlas.EllipticCurves.code.IsogenyKernels
open Polynomial

variable {E : ShortWeierstrassCurve k}


namespace VeluDeg2Data

variable (d : VeluDeg2Data E)

/-- The $x$-coordinate of the Vélu degree-2 isogeny:
$\varphi_x(x) = \frac{x^2 - x_0 x + t}{x - x_0}$. -/
noncomputable def φ_x (x : k) : k := (x ^ 2 - d.x₀ * x + d.t) / (x - d.x₀)

/-- Multiplier appearing in the $y$-coordinate of the Vélu degree-2 isogeny:
$\frac{(x - x_0)^2 - t}{(x - x_0)^2}$, so that $\varphi_y(x, y) = y \cdot
\frac{(x - x_0)^2 - t}{(x - x_0)^2}$. -/
noncomputable def φ_y_coeff (x : k) : k := ((x - d.x₀) ^ 2 - d.t) / (x - d.x₀) ^ 2

/-- The (generator of the) Vélu degree-2 kernel: the $2$-torsion point $(x_0, 0)$
on $E$. -/
def kernelPoint : AffinePoint E :=
  ⟨d.x₀, 0, d.kernel_point_on_curve⟩

end VeluDeg2Data

/-- Vélu's per-point parameter $t_Q = 3 x_Q^2 + A$ at the point $Q = (x_Q, y_Q)$. -/
def AffinePoint.tQ (Q : AffinePoint E) : k := 3 * Q.x ^ 2 + E.A

/-- Vélu's per-point parameter $u_Q = 2 y_Q^2$ at the point $Q$. -/
def AffinePoint.uQ (Q : AffinePoint E) : k := 2 * Q.y ^ 2

/-- Vélu's per-point parameter $w_Q = u_Q + t_Q x_Q$ at the point $Q$. -/
def AffinePoint.wQ (Q : AffinePoint E) : k := Q.uQ + Q.tQ * Q.x

