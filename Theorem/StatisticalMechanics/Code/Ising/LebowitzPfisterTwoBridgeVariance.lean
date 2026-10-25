/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoBridgeVariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterSingleBridgeVariance.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoBridgeVariance


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


@[simp] theorem replicaBridgeInteraction_twoBridgeSites
    (x y : V) (a b : ConfigSpace V) :
    replicaBridgeInteraction (twoBridgeSites x y) a b =
      spin a x * spin b x + spin a y * spin b y := by
  unfold replicaBridgeInteraction twoBridgeSites
  rw [Fintype.sum_bool]
  simp only
  ring

theorem replicaBridgeMoment_twoBridgeSites_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (x y : V) (r : Real) :
    replicaBridgeMoment G J hf (twoBridgeSites x y) r =
      twoReplicaTwoBridgeMoment G J hf x y r := by
  unfold replicaBridgeMoment twoReplicaTwoBridgeMoment
  congr 1
  funext a b
  rw [replicaBridgeInteraction_twoBridgeSites]


end
end StatMech.Ising
