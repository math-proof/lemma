/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheJacobianStability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheLocalAnalytic.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheJacobianSign
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheJacobianStability
open Finset Filter Topology Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexAnisotropyMagnitude (c : Real) : Real :=
  -sixVertexDelta c

end
end StatMech.FrontierD
