/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/PermCycleQuotientWeightSum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.PermOrbitWeightSum
import Theorem.StatisticalMechanics.Code.FrontierA.PermCycleQuotientCount.Part2
import Instance.StatisticalMechanics.Code.FrontierD.PermCycleQuotientWeightSum
open Equiv Finset


namespace StatMech.FrontierD

noncomputable section

def permCycleQuotientWeightSum
    {D A : Type*} [Fintype D] [DecidableEq D] [AddCommMonoid A]
    (sigma : Perm D) (C : StatMech.FrontierA.PermCycleClass sigma)
    (f : D → A) : A := by
  classical
  exact ∑ x : D, if C = Quot.mk _ x then f x else 0


end
end StatMech.FrontierD
