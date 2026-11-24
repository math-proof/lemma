module
public import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentParity.Part2
public import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge.Part7
public import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentParityLift
open MeasureTheory
open scoped BigOperators ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParityLift.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def parityCurrentTerm (beta : ℝ) (k : ℕ) : ℝ :=
  beta ^ k / k.factorial

end StatMech.FrontierB
