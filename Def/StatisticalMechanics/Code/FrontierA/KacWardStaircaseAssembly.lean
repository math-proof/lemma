/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIncidentStairPatch.Part2
import Structure.StatisticalMechanics.Code.FrontierA.KacWardStaircaseAssembly


namespace StatMech.FrontierA

open scoped NNReal

open Set


noncomputable def kwEndpointParameter (M : ℕ) (beta alpha : ℝ)
    (k : Fin (M + 3)) : ℝ :=
  if k.val = 0 then 0
  else if k.val = M + 2 then 1
  else beta + ((k.val - 1 : ℕ) : ℝ) / M * (1 - alpha - beta)

end StatMech.FrontierA
