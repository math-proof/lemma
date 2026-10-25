/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalWitnessStep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutFreeLaw.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalWitnessStep
open scoped BigOperators
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech

instance instDecidableFalseBoundary (R : FKRectTorus) :
    DecidablePred (fun _ : R.Vertex => False) :=
  fun _ => isFalse id


end
end StatMech.FrontierD
