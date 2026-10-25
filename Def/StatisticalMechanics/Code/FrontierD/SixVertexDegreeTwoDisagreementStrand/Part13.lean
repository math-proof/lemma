/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentCType.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part5
import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part11
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def permOrderedAllCycles
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) : List D :=
  sigma.cycleFactorsFinset.toList.flatMap fun cycle =>
    if hcycle : cycle ∈ sigma.cycleFactorsFinset then
      permOrderedCycleFactor sigma cycle hcycle
    else []

end
end StatMech.FrontierD
