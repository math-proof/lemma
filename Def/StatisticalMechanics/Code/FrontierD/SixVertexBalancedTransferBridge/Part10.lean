/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedBoundaryGluing
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexParticleHole.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part9
open Finset Matrix


namespace StatMech.FrontierD

noncomputable def svTorusBalancedArrowPartitionSum
    (T : EvenTorus) (c : Real) : Real :=
  ∑ omega : SixVertexArrows T,
    if (sixVertexTorusSeam T omega).Balanced then omega.weight c else 0

end StatMech.FrontierD
