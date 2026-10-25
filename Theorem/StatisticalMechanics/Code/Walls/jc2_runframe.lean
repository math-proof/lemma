/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_runframe.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc_earanchor.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc_toprowrun.Part4
import Theorem.StatisticalMechanics.Code.Walls.jc_runnoup
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc2_isTopRowRun_of_extremeCell (K : Set (Site 2)) (hK : K.Finite) (c : Site 2)
    (hc : IsExtremeCell K c) : jc_IsTopRowRun K c (jc_runMax K c : ℤ) where
  isExtreme := hc
  len_nonneg := by positivity
  run_mem := by
    intro j hj0 hj1
    
    have hjnat : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj0
    have hle : j.toNat ≤ jc_runMax K c := by omega
    have hmem := jc_runMax_mem K hK c hc.mem j.toNat hle
    rw [jc_shiftX] at hmem
    rwa [hjnat] at hmem
  right_stop := by
    have hns := jc_runMax_succ_nmem_K K hK c hc.mem
    rw [jc_shiftX] at hns
    exact hns


end Walls
end StatMech
