/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheScattering.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricProduct.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part9
import Mathlib.GroupTheory.Perm.Fin
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBethe
open Finset Matrix
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

def sixVertexBethePairFactor (c : ℝ) (u v : ℂ) : ℂ :=
  1 + u * v - 2 * sixVertexDelta c * u

end
end StatMech.FrontierD
