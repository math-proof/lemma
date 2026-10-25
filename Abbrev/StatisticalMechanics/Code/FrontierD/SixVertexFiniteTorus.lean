/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFiniteTorus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Mathlib.LinearAlgebra.Matrix.Trace
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part2
open Finset Matrix


namespace StatMech.FrontierD

abbrev MatrixCompatibleCycle {α : Type*} [Fintype α] {M : ℕ}
    (hM : 0 < M) (A : Matrix α α ℝ) :=
  {x : Fin M → α // ∀ i, A (x i) (x (finitePeriodicSucc hM i)) ≠ 0}


end StatMech.FrontierD
