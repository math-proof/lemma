/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWidthFreeEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFreeEnergy
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWidthFreeEnergy.Part2
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable def sixVertexFixedWidthPartitionSum (N M : ℕ) (c : ℝ) : ℝ :=
  Matrix.trace (sixVertexTransfer N c ^ M)


end StatMech.FrontierD
