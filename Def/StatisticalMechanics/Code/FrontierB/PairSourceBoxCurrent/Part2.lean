module
public import Theorem.StatisticalMechanics.Code.FrontierB.SourceCurrentTail.Part3
public import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
public import Theorem.StatisticalMechanics.Code.FrontierB.BoxCurrentLaws.Part3
public import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentPairLaw.Part2
public import Theorem.StatisticalMechanics.Code.FrontierB.PairSourceBoxCurrent.Part2
open MeasureTheory
open scoped ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceBoxCurrent.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierB

open Sharpness Lattice


noncomputable def boxPairCorrelationConstant
    (d n : ℕ) (beta : ℝ)
    (x y : StatMech.FK.boxVerts d n) : ℝ :=
  pathCorrelationConstant (StatMech.FK.boxGraph d n) beta
    (fun _ => 1) Finset.univ (boxGraphPath d n x y)

end StatMech.FrontierB
