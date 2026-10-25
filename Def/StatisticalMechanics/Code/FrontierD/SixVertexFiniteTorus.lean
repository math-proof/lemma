/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFiniteTorus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Mathlib.LinearAlgebra.Matrix.Trace
open Finset Matrix


namespace StatMech.FrontierD

def finitePeriodicSucc {M : ℕ} (hM : 0 < M) (i : Fin M) : Fin M :=
  ⟨(i.val + 1) % M, Nat.mod_lt _ hM⟩

end StatMech.FrontierD
