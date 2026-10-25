/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectedMatchingCut
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Structure.StatisticalMechanics.Code.Ising.LebowitzPfisterFiveCurrentPairing
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.GhostCurrentRep

noncomputable section

variable {W : Type*} [DecidableEq W]


def lpFiveToggle12 (T : Finset W)
    (a : LPFiveSourceAllocation W) : LPFiveSourceAllocation W where
  source1 := a.source1 ∆ T
  source2 := a.source2 ∆ T
  source3 := a.source3
  source4 := a.source4
  source5 := a.source5


def lpFiveToggle14 (T : Finset W)
    (a : LPFiveSourceAllocation W) : LPFiveSourceAllocation W where
  source1 := a.source1 ∆ T
  source2 := a.source2
  source3 := a.source3
  source4 := a.source4 ∆ T
  source5 := a.source5


def lpFiveToggle23 (T : Finset W)
    (a : LPFiveSourceAllocation W) : LPFiveSourceAllocation W where
  source1 := a.source1
  source2 := a.source2 ∆ T
  source3 := a.source3 ∆ T
  source4 := a.source4
  source5 := a.source5


def LPFiveSourceAllocation.total
    (a : LPFiveSourceAllocation W) : Finset W :=
  lpFiveSourceTotal a.source1 a.source2 a.source3 a.source4 a.source5


def lpFiveOrbitABPos (Si Sj T : Finset W) : LPFiveSourceAllocation W :=
  ⟨Si ∆ Sj ∆ T, ∅, ∅, ∅, ∅⟩


def lpFiveOrbitABNeg (Si Sj T : Finset W) : LPFiveSourceAllocation W :=
  ⟨Si ∆ Sj, T, ∅, ∅, ∅⟩


end
end StatMech.Ising
