/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCorrections.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
import Def.StatisticalMechanics.Code.FrontierA.GrahamCorrections.Part2


namespace StatMech.FrontierA

open Finset

open scoped symmDiff

open StatMech.Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem grahamBridgeGap_comm (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i k m : V) :
    grahamBridgeGap E J i k m = grahamBridgeGap E J k i m := by
  unfold grahamBridgeGap
  rw [grahamTwoPoint_comm E J i k, grahamTwoPoint_comm E J i m,
    grahamTwoPoint_comm E J m k]
  ring


end StatMech.FrontierA
