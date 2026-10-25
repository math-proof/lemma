/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFiniteTorus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Mathlib.LinearAlgebra.Matrix.Trace
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus
open Finset Matrix


namespace StatMech.FrontierD

noncomputable def matrixCompatibleCycleSum {α : Type*} [Fintype α]
    {M : ℕ} (hM : 0 < M) (A : Matrix α α ℝ) : ℝ :=
  ∑ x : MatrixCompatibleCycle hM A, matrixCycleWeight hM A x

def matrixChainWeight {α : Type*} [Fintype α] {k : ℕ}
    (A : Matrix α α ℝ) (x : Fin (k + 1) → α) (b : α) : ℝ :=
  (∏ i : Fin k, A (x i.castSucc) (x i.succ)) * A (x (Fin.last k)) b

end StatMech.FrontierD
