/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterAgreementMarginalRatio.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeActual.Part2
open Finset SimpleGraph


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


def agreementConfigFinsetEquiv : ConfigSpace V ≃ Finset V where
  toFun := ghsLAgreeFinset
  invFun := fun S v => decide (v ∈ S)
  left_inv := by
    intro q
    funext v
    cases hq : q v <;> simp [ghsLAgreeFinset, hq]
  right_inv := by
    intro S
    ext v
    simp [ghsLAgreeFinset]

end
end StatMech.Ising
