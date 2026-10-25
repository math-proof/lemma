/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part15
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannel_fullDualProjection_and_discardedBits_injective
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective (fun omega : RlcTwoChannelEdgeConfig gamma gamma' =>
      ((fun e : RlcTwoChannelFullVariableTargetEdge gamma gamma' =>
          rlc_twoChannelFullDualConfig gamma gamma' omega e.1),
        fun e : RlcTwoChannelFullDiscardedSourceEdge gamma gamma' =>
          omega e.1)) := by
  intro omega omega' hpair
  have hvisible := congrArg Prod.fst hpair
  have hdiscarded := congrArg Prod.snd hpair
  funext source
  by_cases hrange : source ∈ Set.range
      (rlc_twoChannelFullSourceEdge (gamma := gamma) (gamma' := gamma'))
  · obtain ⟨target, htarget⟩ := hrange
    have hcoord := congrFun hvisible target
    change rlc_twoChannelFullDualConfig gamma gamma' omega target.1 =
      rlc_twoChannelFullDualConfig gamma gamma' omega' target.1 at hcoord
    rw [rlc_twoChannelFullDualConfig_of_source gamma gamma' omega target.1
        source (by rw [← htarget, rlc_twoChannelFullSourceEdge_map]),
      rlc_twoChannelFullDualConfig_of_source gamma gamma' omega' target.1
        source (by rw [← htarget, rlc_twoChannelFullSourceEdge_map])] at hcoord
    exact Bool.not_injective hcoord
  · exact congrFun hdiscarded ⟨source, hrange⟩


end
end StatMech.Universality
