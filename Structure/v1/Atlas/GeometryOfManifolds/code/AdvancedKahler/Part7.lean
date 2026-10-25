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
import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part7
set_option autoImplicit false

open DifferentialFormSpace


/-- A uniform-in-norm constant $c_G > 0$ such that for every $k \ne 0$ and
$s \in \Omega^0$, $\|G(s)\|_{L^2}^2 \le (c_G/k)\, \|\bar\partial s\|_{L^2}^2$.
This expresses the spectral gap of $\bar\square$ uniformly across $L^k$. -/
structure UniformGreenL2Bound
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (greenOp : ∀ (l2 : L2NormSpace Ω (inst := inst)) (dol : DolbeaultOps (inst := inst)),
      HasGreenOperator Ω l2 dol)
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst)) where
  c_G : ℝ
  c_G_pos : c_G > 0
  uniform_bound : ∀ (k : ℕ) (hk : k ≠ 0) (s : Ω 0),
    l2.l2norm ((greenOp l2 dol).greenCorrection k s) *
      l2.l2norm ((greenOp l2 dol).greenCorrection k s) ≤
      c_G / (k : ℝ) * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s))

