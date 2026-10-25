/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteBidegreeCumulativeHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FiniteCumulativeGradeHall
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteBidegreeCumulativeHall
open Finset


namespace StatMech.FrontierD

noncomputable section

structure TwoBranchMonotoneEmbeddings
    (Source Target : Type*) (sourceGrade : Source → Nat)
    (targetGrade : Target → Nat) where
  branch : Bool → Source ↪ Target
  distinct : ∀ source, branch false source ≠ branch true source
  monotone : ∀ choice source,
    sourceGrade source ≤ targetGrade (branch choice source)

end
end StatMech.FrontierD
