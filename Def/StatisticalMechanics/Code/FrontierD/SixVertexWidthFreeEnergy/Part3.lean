/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWidthFreeEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFreeEnergy
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWidthFreeEnergy.Part3
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable def sixVertexWidthMaxSectorCount (N : ℕ) (c : ℝ) : ℝ :=
  ∑ n : Fin (N + 1),
    if sixVertexWidthSectorTopEigenvalue N c n = sixVertexWidthTopEigenvalue N c
    then 1 else 0

end StatMech.FrontierD
