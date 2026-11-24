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
public import Def.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part6
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


theorem middleSwap_involutive (m : Finset ι) (c : ↑m → Fin 4) :
    middleSwap m (middleSwap m c) = c := by
  funext i
  simp [middleSwap]

theorem colorClass_middleSwap (m : Finset ι) (c : ↑m → Fin 4) (a : Fin 4) :
    colorClass m (middleSwap m c) a = colorClass m c (Equiv.swap (1 : Fin 4) 2 a) := by
  ext i
  by_cases hi : i ∈ m
  · simp [colorClass, middleSwap, Equiv.swap_apply_def, hi]
    aesop
  · simp [colorClass, hi]


end FourColor
end GrahamGHS
end StatMech
