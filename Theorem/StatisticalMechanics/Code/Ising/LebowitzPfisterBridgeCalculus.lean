/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterBridgeCalculus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part11
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterBridgeCalculus
open Finset Filter
open scoped BigOperators


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]


theorem replicaBridgeInteraction_mate
    (sites : I -> V) (q a : ConfigSpace V) :
    replicaBridgeInteraction sites a (ghsLMate q a) =
      replicaAgreementSpin sites q := by
  unfold replicaBridgeInteraction replicaAgreementSpin
  apply Finset.sum_congr rfl
  intro i hi
  unfold ghsLMate spin
  by_cases hq : q (sites i) <;>
    by_cases ha : a (sites i) <;> simp [hq, ha]


end
end StatMech.Ising
