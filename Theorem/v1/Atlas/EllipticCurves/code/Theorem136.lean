/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem136.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.OrdinarySupersingular
import Lemma.Complex.Atlas.v1.EllipticCurves.code.OrdinarySupersingular
import Lemma.Complex.Atlas.v1.EllipticCurves.code.PointCounting
import Lemma.Complex.Atlas.v1.EllipticCurves.code.EndAlgebra
import Def.v1.Atlas.EllipticCurves.code.PointCounting.Part2
import Instance.v1.Atlas.EllipticCurves.code.EndAlgebra.Part5
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Dimension.Finrank
import Def.v1.Atlas.EllipticCurves.code.Theorem136
open Module Polynomial
open scoped TensorProduct

universe u


namespace EllipticCurve

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

/-- The polynomial $X^2 - \Delta_\pi$ is nonzero. -/
lemma endPoly_ne_zero (W : WeierstrassCurve.Affine F) : endPoly W ≠ 0 :=
  X_pow_sub_C_ne_zero (by norm_num : 0 < 2) _

/-- The polynomial $X^2 - \Delta_\pi$ has degree $2 \neq 0$, which guarantees that
`AdjoinRoot (endPoly W)` is nontrivial. -/
lemma endPoly_degree_ne_zero (W : WeierstrassCurve.Affine F) :
    (endPoly W).degree ≠ 0 := by
  unfold endPoly
  simp [degree_X_pow_sub_C (by norm_num : 0 < 2)]

end EllipticCurve
