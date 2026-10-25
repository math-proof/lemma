/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part6
set_option autoImplicit false

open DifferentialFormSpace


/-- Every compact symplectic manifold (of complex dimension $n$) is a compact manifold
of real dimension $2n$. -/
instance (priority := 100) IsCompactSymplectic.toIsCompactManifold
    {Ω : ℕ → Type*} {VF : Type*} [DifferentialFormSpace Ω VF]
    [h : IsCompactSymplectic Ω VF] : IsCompactManifold Ω VF where
  dim := 2 * h.n
  dim_pos := Nat.mul_pos (by norm_num) h.n_pos

