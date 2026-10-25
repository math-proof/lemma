/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Reparameterization.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part4


namespace StatMech

namespace Exact3D

namespace FKReparameterization

set_option linter.style.longLine false in


noncomputable def pOfBetaLeftPullbackWindow
    (βc : ℝ) (pWindow : ℝ → ℝ)
    (pWindow_pos : ∀ ε, 0 < ε → 0 < pWindow ε) (ε : ℝ) : ℝ :=
  if hε : 0 < ε then
    Classical.choose
      (exists_pOfBeta_mem_Ioo_left (βc := βc) (pδ := pWindow ε)
        (pWindow_pos ε hε))
  else
    1

end FKReparameterization
end Exact3D
end StatMech
