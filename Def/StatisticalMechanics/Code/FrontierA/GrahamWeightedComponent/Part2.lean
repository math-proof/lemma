/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedComponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.gh4eq22.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsing.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.Claim1IsingFull.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedComponent
open Finset SimpleGraph
open scoped symmDiff


namespace StatMech.FrontierA

open StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Walls

variable {ι W : Type*} [DecidableEq ι] [Fintype ι]
  [DecidableEq W] [Fintype W]


noncomputable def grahamSuperpositionBondComponent
    (ends : ι → Sym2 W) (m : Finset ι) (u : W) : Finset ι :=
  gh4_bondCompOf ends m u


end StatMech.FrontierA
