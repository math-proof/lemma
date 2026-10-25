/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularDualPath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopDisorderKacWard
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCriticalWeight
import Abbrev.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Sharpness

noncomputable section

def ons_rectDualAdj (M N : Nat) (u v : ons_RectDualVertex M N) : Prop :=
  (u.2 = v.2 ∧ Nat.dist u.1.val v.1.val = 1) ∨
    (u.1 = v.1 ∧ Nat.dist u.2.val v.2.val = 1)

end
end StatMech.Onsager
