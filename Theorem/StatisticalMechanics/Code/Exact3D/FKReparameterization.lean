/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Reparameterization.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2
import Def.StatisticalMechanics.Code.Exact3D.FKReparameterization


namespace StatMech

namespace Exact3D

namespace FKReparameterization

theorem pOfBeta_strictMono : StrictMono IsingFK.pOfBeta := by
  intro a b hab
  unfold IsingFK.pOfBeta
  have h_exp : Real.exp (-2 * b) < Real.exp (-2 * a) := by
    rw [Real.exp_lt_exp]
    linarith
  linarith


theorem hasDerivAt_pOfBeta (β : ℝ) :
    HasDerivAt IsingFK.pOfBeta (2 * Real.exp (-2 * β)) β := by
  unfold IsingFK.pOfBeta
  have hlin : HasDerivAt (fun x : ℝ => -2 * x) (-2) β := by
    simpa using (hasDerivAt_id β).const_mul (-2)
  have hexp :
      HasDerivAt (fun x : ℝ => Real.exp (-2 * x))
        (Real.exp (-2 * β) * (-2)) β := by
    simpa using hlin.exp
  have hone : HasDerivAt (fun _x : ℝ => (1 : ℝ)) 0 β :=
    hasDerivAt_const β 1
  have hsub := hone.sub hexp
  convert hsub using 1
  ring


end FKReparameterization
end Exact3D
end StatMech
