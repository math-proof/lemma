/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangPressurePrimitive.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxSpinLimit
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangLocalCorrelationReduction
open Complex Filter MeasureTheory Metric Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.FK StatMech.Ising StatMech.Lattice StatMech.FrontierB
  StatMech.FrontierC StatMech.Sharpness StatMech.Sharpness.FieldGhostDict


noncomputable def leeYangSpinProductRightEnvelope
    (beta : ℝ) (A : Finset (Site d)) (h : ℂ) : ℝ :=
  let r := ‖Complex.exp (-2 * (beta : ℂ) * h)‖
  ((1 + r) / (1 - r)) ^ A.card


noncomputable def leeYangSpinProductLeftEnvelope
    (beta : ℝ) (A : Finset (Site d)) (h : ℂ) : ℝ :=
  let r := ‖Complex.exp (2 * (beta : ℂ) * h)‖
  ((1 + r) / (1 - r)) ^ A.card

end StatMech.FrontierA
