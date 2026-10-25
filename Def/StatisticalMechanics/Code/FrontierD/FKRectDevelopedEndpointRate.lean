/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointRate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedEndpointSpan
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def fkRectDevelopedReflectedEndpointLowerOf
    (crossingFloor : Real) (n : Nat) : Real :=
  (crossingFloor / (((3 * n + 1) ^ 2 : Nat) : Real)) ^ 2

end
end StatMech.FrontierD
