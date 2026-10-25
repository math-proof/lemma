/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWidthFreeEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFreeEnergy
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

theorem sixVertexWidthSectorIndex_le (N : ℕ) (n : Fin (N + 1)) : n.val ≤ N := by
  omega


end StatMech.FrontierD
