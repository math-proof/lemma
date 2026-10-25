/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectedMatchingCut
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterFiveCurrentPairing.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.GhostCurrentRep

noncomputable section

variable {W : Type*} [DecidableEq W]


theorem lpFiveToggle23_orbitCD
    (Si Sj T : Finset W) :
    lpFiveToggle23 T (lpFiveOrbitCDNeg Si Sj T) =
      lpFiveOrbitCDPos Si Sj T := by
  apply LPFiveSourceAllocation.ext <;>
    simp only [lpFiveToggle23, lpFiveOrbitCDNeg, lpFiveOrbitCDPos]
  all_goals
    ext x
    simp only [Finset.mem_symmDiff, Finset.notMem_empty]
    tauto


end
end StatMech.Ising
