/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearHomotopyReduction.Part2
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Def.StatisticalMechanics.Code.FrontierA.KacWardRectilinearSeparation


namespace StatMech.FrontierA

open scoped Convex Pointwise

open scoped NNReal ENNReal

open Set


instance {n : ℕ} [NeZero n] (i j : Fin n) :
    Decidable (KWEdgesNonincident i j) := by
  unfold KWEdgesNonincident
  infer_instance

end StatMech.FrontierA
