/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectedMatchingCut
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFiveCurrentPairing.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.GhostCurrentRep

noncomputable section

variable {W : Type*} [DecidableEq W]


def lpFiveOrbitCDNeg (Si Sj T : Finset W) : LPFiveSourceAllocation W :=
  ⟨Si, Sj ∆ T, ∅, ∅, ∅⟩

def lpFiveOrbitCDPos (Si Sj T : Finset W) : LPFiveSourceAllocation W :=
  ⟨Si, Sj, T, ∅, ∅⟩

end
end StatMech.Ising
