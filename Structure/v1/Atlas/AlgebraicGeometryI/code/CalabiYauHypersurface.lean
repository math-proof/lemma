/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CalabiYauHypersurface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
set_option maxHeartbeats 400000


namespace CYHyp

/-- Auxiliary record of numerical invariants of a smooth complete curve: its genus `g` and
canonical degree `degK`. -/
structure SmoothCompleteCurve' where
  g : ℤ
  degK : ℤ

end CYHyp
