module
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectedMatchingCut
public import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
public import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterFiveCurrentPairing.Part2
open Finset
open scoped symmDiff


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.GhostCurrentRep

noncomputable section

variable {W : Type*} [DecidableEq W]


theorem lpFiveToggle14_orbitEF
    (Si Sj T : Finset W) :
    lpFiveToggle14 T (lpFiveOrbitEFNeg Si Sj T) =
      lpFiveOrbitEFPos Si Sj T := by
  apply LPFiveSourceAllocation.ext <;>
    simp only [lpFiveToggle14, lpFiveOrbitEFNeg, lpFiveOrbitEFPos]
  all_goals
    ext x
    simp only [Finset.mem_symmDiff, Finset.notMem_empty]
    tauto


end
end StatMech.Ising
