/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RandomWalkHighDimensionalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Theorem.StatisticalMechanics.Code.Sharpness.IsingSharpness
import Theorem.StatisticalMechanics.Code.FrontierA.RandomWalkHighDimensionalReduction.Part2
open Filter Finset Topology


namespace StatMech.FrontierA

noncomputable def highDimensionalRandomWalkTail
    (d : ℕ) (epsilon sigma C c xi radius : ℝ) : ℝ :=
  C / sigma ^ d *
    Real.rpow (sigma / max sigma radius) ((d : ℝ) - 2 - epsilon) *
      Real.exp (-c * radius / xi)


end StatMech.FrontierA
