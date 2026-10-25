/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorPerronLogConcavity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCentralSectorDominance.Part2
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexSectorPerronProfile
    (N : Nat) (c : Real) (n : Nat) : Real :=
  sixVertexSectorTopEigenvalue N (min n N) (min_le_right n N) c

end
end StatMech.FrontierD
