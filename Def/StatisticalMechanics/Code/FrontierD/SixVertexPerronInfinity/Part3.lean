/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDefectDynamics.Part7
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerronInfinity.Part3
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexNoAdjacentZeroExtend {N n : Nat}
    (q : SixVertexNoAdjacentSector N n → Real) : SixVertexSector N n → Real := by
  classical
  exact fun x => if hx : SixVertexSectorNoAdjacent x then q ⟨x, hx⟩ else 0

end
end StatMech.FrontierD
