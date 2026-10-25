/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ConnectionsCurvature
import Structure.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part7
import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part6
set_option autoImplicit false

open DifferentialFormSpace


/-- Helper: from a squared bound $a^2 \le (C/k) b^2$ with $a, b \ge 0$ and
$C/k \ge 0$, conclude the linear bound $a \le \sqrt{C/k}\, b$. -/
theorem l2_bound_from_squared_bound
    {a b C : ℝ} {k : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hCk : 0 ≤ C / (k : ℝ))
    (hsq : a * a ≤ C / (k : ℝ) * (b * b)) :
    a ≤ Real.sqrt (C / (k : ℝ)) * b := by
  have h1 : Real.sqrt (a * a) ≤ Real.sqrt (C / (k : ℝ) * (b * b)) :=
    Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_mul_self ha] at h1
  rw [Real.sqrt_mul hCk, Real.sqrt_mul_self hb] at h1
  exact h1


