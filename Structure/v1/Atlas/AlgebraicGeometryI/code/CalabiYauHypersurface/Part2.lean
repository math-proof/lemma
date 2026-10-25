/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Def.v1.Atlas.AlgebraicGeometryI.code.CalabiYauHypersurface
set_option maxHeartbeats 400000

open CYHyp


noncomputable section

/-- A smooth projective hypersurface in `P^n` of degree `d`, with `n, d ≥ 1`. -/
structure SmoothProjectiveHypersurface where
  n : ℕ
  d : ℕ
  hn : 1 ≤ n
  hd : 1 ≤ d

end
