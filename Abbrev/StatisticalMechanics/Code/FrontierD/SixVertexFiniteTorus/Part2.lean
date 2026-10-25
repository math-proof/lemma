/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFiniteTorus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Mathlib.LinearAlgebra.Matrix.Trace
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part2
open Finset Matrix


namespace StatMech.FrontierD

abbrev SixVertexPeriodicRows (N M : ℕ) (hM : 0 < M) (c : ℝ) :=
  MatrixCompatibleCycle hM (sixVertexTransfer N c)


end StatMech.FrontierD
