/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentTail.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.LocalCurrentTail.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.BoundaryCurrentTail
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def boundaryPartitionJ (beta : ℝ) (J : Sym2 V → ℝ)
    (interior : Finset V) : ℝ :=
  ∑ s : ConfigSpace ↑interior,
    boltzmannJ G beta J (extendInteriorPlus interior s)

end StatMech.FrontierB
