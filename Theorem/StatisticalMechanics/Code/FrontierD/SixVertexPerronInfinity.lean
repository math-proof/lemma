/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDefectDynamics.Part7
import Mathlib.Analysis.InnerProductSpace.Rayleigh
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexNoAdjacentTransferInfinity_isHermitian (N n : Nat) :
    (sixVertexNoAdjacentTransferInfinity N n).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro x y
  simp only [star_id_of_comm]
  exact sixVertexNoAdjacentTransferInfinity_symmetric N n y x

end
end StatMech.FrontierD
