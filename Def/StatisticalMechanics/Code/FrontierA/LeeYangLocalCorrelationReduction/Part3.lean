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
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangLocalCorrelationReduction.Part2
open Complex Filter MeasureTheory Metric Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.FK StatMech.Ising StatMech.Lattice StatMech.FrontierB
  StatMech.FrontierC StatMech.Sharpness StatMech.Sharpness.FieldGhostDict


def LeeYangSpinProductRightBound
    (d : ℕ) (beta : ℝ) (A : Finset (Site d)) : Prop :=
  ∀ n h, 0 < h.re →
    ‖leeYangBoxSpinProduct d beta A n h‖ ≤
      leeYangSpinProductRightEnvelope beta A h


def LeeYangSpinProductLeftBound
    (d : ℕ) (beta : ℝ) (A : Finset (Site d)) : Prop :=
  ∀ n h, h.re < 0 →
    ‖leeYangBoxSpinProduct d beta A n h‖ ≤
      leeYangSpinProductLeftEnvelope beta A h


end StatMech.FrontierA
