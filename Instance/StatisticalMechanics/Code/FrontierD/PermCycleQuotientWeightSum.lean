/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/PermCycleQuotientWeightSum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.PermOrbitWeightSum
import Theorem.StatisticalMechanics.Code.FrontierA.PermCycleQuotientCount.Part2
open Equiv Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable instance permCycleClassFintype
    {D : Type*} [Fintype D] [DecidableEq D] (sigma : Perm D) :
    Fintype (StatMech.FrontierA.PermCycleClass sigma) :=
  Fintype.ofEquiv
    (StatMech.FrontierA.PermCycleRepresentative sigma)
    (StatMech.FrontierA.permCycleClassEquivRepresentative sigma).symm


end
end StatMech.FrontierD
