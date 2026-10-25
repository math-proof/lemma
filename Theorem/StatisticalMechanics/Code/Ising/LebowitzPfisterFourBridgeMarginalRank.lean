/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMarginalRank.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterAgreementMarginalRatio.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeActual.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeMarginalRank
open Finset SimpleGraph


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


@[simp] theorem agreementConfigFinsetEquiv_apply (q : ConfigSpace V) :
    agreementConfigFinsetEquiv q = ghsLAgreeFinset q := rfl

@[simp] theorem agreementConfigFinsetEquiv_symm_apply (S : Finset V) (v : V) :
    agreementConfigFinsetEquiv.symm S v = decide (v ∈ S) := rfl


end
end StatMech.Ising
