module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
public import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
public import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
public import Theorem.StatisticalMechanics.Code.Ising.GHSThreePoint
public import Theorem.StatisticalMechanics.Code.Walls.ghc_urselleqgap
public import Theorem.StatisticalMechanics.Code.Walls.gc_ergrep
public import Theorem.StatisticalMechanics.Code.Walls.gc_core
open scoped BigOperators symmDiff
open Finset SimpleGraph Set
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc_core.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech.Ising StatMech.Sharpness

open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def GHSSignDominance (β h : ℝ) (o : V) : Prop :=
  ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → eg_ursell3 G β h o x y ≤ 0


end StatMech.Walls
