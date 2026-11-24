module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
public import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
public import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
public import Theorem.StatisticalMechanics.Code.Ising.GHSThreePoint
public import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
public import Theorem.StatisticalMechanics.Code.Ising.CurrentWeight.Part2
public import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
public import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePropsFull.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
public import Theorem.StatisticalMechanics.Code.Walls.gc10ghostfourpoint
public import Theorem.StatisticalMechanics.Code.Walls.ghc_urselleqgap
public import Theorem.StatisticalMechanics.Code.Walls.vbgtriangle.Part3
public import Theorem.StatisticalMechanics.Code.Walls.gc7ghosteven
public import Def.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part9
open scoped BigOperators symmDiff
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace GrahamGHS

open Ising

open Sharpness


namespace FourColor

variable {W ι : Type*} [Fintype W] [DecidableEq W] [Fintype ι] [DecidableEq ι]


theorem balancedSwap_involutive (m X Y : Finset ι) (c : ↑m → Fin 4) :
    balancedSwap m X Y (balancedSwap m X Y c) = c := by
  funext i
  have hci : c i = 0 ∨ c i = 1 ∨ c i = 2 ∨ c i = 3 := by omega
  rcases hci with hci | hci | hci | hci <;>
    by_cases hiX : (i : ι) ∈ X <;> by_cases hiY : (i : ι) ∈ Y <;>
      simp [balancedSwap, middleSwapOn, outerSwapOn, hiX, hiY,
        Equiv.swap_apply_def, hci]


end FourColor
end GrahamGHS
end StatMech
