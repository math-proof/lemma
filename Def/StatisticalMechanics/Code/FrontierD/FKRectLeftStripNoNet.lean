/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLeftStripNoNet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAugmentedBarrierWindingMass.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectLeftStripNoNet
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def FKRectLeftStripTouchesRight (R : FKRectTorus)
    (omega : R.Configuration) (right : Nat) (v : R.Vertex) : Prop :=
  ∃ hv : v ∈ fkRectLeftStrip R right,
    ∃ y : fkRectLeftStrip R right,
      y.1.1.val = right ∧
        FKRectConnectedWithin R omega (fkRectLeftStrip R right)
          ⟨v, hv⟩ y


def fkRectLeftStripRightPotential (R : FKRectTorus)
    (omega : R.Configuration) (right : Nat) (v : R.Vertex) : Int := by
  classical
  exact if v ∈ fkRectLeftStrip R right then
    if FKRectLeftStripTouchesRight R omega right v then 1 else 0
  else 1

end
end StatMech.FrontierD
