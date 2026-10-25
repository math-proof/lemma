/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointRate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedEndpointSpan
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedEndpointRate
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def fkRectDevelopedReflectedEndpointLower (q : Real) (n : Nat) : Real :=
  fkRectDevelopedReflectedEndpointLowerOf (1 / (2 * (1 + q))) n

end
end StatMech.FrontierD
