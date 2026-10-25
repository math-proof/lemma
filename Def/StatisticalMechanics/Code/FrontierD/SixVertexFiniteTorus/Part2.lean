/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFiniteTorus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Mathlib.LinearAlgebra.Matrix.Trace
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus
open Finset Matrix


namespace StatMech.FrontierD

def matrixCycleWeight {α : Type*} [Fintype α] {M : ℕ} (hM : 0 < M)
    (A : Matrix α α ℝ) (x : Fin M → α) : ℝ :=
  ∏ i, A (x i) (x (finitePeriodicSucc hM i))


end StatMech.FrontierD
