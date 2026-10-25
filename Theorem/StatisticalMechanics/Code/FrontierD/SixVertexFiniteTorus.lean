/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFiniteTorus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Mathlib.LinearAlgebra.Matrix.Trace
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus
open Finset Matrix


namespace StatMech.FrontierD

@[simp] theorem finitePeriodicSucc_castSucc {M : ℕ} (i : Fin M) :
    finitePeriodicSucc (Nat.succ_pos M) i.castSucc = i.succ := by
  ext
  simp [finitePeriodicSucc, Nat.mod_eq_of_lt]

@[simp] theorem finitePeriodicSucc_last (M : ℕ) :
    finitePeriodicSucc (Nat.succ_pos M) (Fin.last M) = 0 := by
  ext
  simp [finitePeriodicSucc]


end StatMech.FrontierD
