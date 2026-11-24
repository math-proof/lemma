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
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part9
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


noncomputable def canonicalMiddleTransfer (ends : ι → Sym2 W) (m : Finset ι)
    (c : ↑m → Fin 4) (k zero : W) : Finset ι :=
  (colorClass m c 1 ∩ edgeComponent ends (rowClass m c 0) zero) ∪
    (colorClass m c 2 ∩ edgeComponent ends (rowClass m c 1) k)


noncomputable def canonicalOuterTransfer (ends : ι → Sym2 W) (m : Finset ι)
    (c : ↑m → Fin 4) (k zero : W) : Finset ι :=
  (colorClass m c 0 ∩ edgeComponent ends (rowClass m c 0) zero) ∪
    (colorClass m c 3 ∩ edgeComponent ends (rowClass m c 1) k)


end FourColor
end GrahamGHS
end StatMech
