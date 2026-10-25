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
import Theorem.v1.Atlas.EllipticCurves.code.IsogenyKernels.Part3
open Polynomial

variable {E : ShortWeierstrassCurve k}


namespace VeluOddData

variable (d : VeluOddData E)

/-- The Vélu odd-degree rational function on $x$-coordinates:
$r(x) = x + \sum_{Q} \left( \frac{t_Q}{x - x_Q} + \frac{u_Q}{(x - x_Q)^2} \right)$. -/
noncomputable def r (x : k) : k :=
  x + d.pts.sum (fun Q => Q.tQ / (x - Q.x) + Q.uQ / (x - Q.x) ^ 2)

/-- Derivative of the Vélu rational function:
$r'(x) = 1 - \sum_{Q} \left( \frac{t_Q}{(x - x_Q)^2} + \frac{2 u_Q}{(x - x_Q)^3} \right)$. -/
noncomputable def r' (x : k) : k :=
  1 + d.pts.sum (fun Q => -(Q.tQ / (x - Q.x) ^ 2) - 2 * Q.uQ / (x - Q.x) ^ 3)

end VeluOddData
