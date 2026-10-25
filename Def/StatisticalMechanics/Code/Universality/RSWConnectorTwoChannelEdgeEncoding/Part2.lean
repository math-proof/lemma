/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelEdgeEncoding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannel.Part9
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelEdgeEncoding
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_twoChannelLiftEdgeFailureEmbedding {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (J : {omega : RlcTwoChannelEdgeConfig gamma gamma' //
          rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
            rlc_finiteTwoChannelConnectorEvent gamma gamma'} ↪
        {eta : RlcTwoChannelEdgeConfig gamma gamma' //
          rlc_twoChannelEdgeConfigExtend gamma gamma' eta ∈
            rlc_finiteTwoChannelConnectorEvent gamma gamma'}) :
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} ↪
      ConfigSpace (Sym2 (RlcConnectorVertex n)) where
  toFun rho :=
    let split := rlc_twoChannelConfigSplitEquiv gamma gamma'
    let edgeFailure : {omega : RlcTwoChannelEdgeConfig gamma gamma' //
        rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
          rlc_finiteTwoChannelConnectorEvent gamma gamma'} :=
      ⟨(split rho.1).1, fun hedge =>
        rho.2 ((rlc_twoChannel_split_fst_mem_event_iff
          gamma gamma' rho.1).mp hedge)⟩
    rlc_twoChannelEdgeConfigCombine gamma gamma'
      (J edgeFailure).1 (split rho.1).2
  inj' := by
    intro rho sigma hrs
    let split := rlc_twoChannelConfigSplitEquiv gamma gamma'
    let rhoEdge : {omega : RlcTwoChannelEdgeConfig gamma gamma' //
        rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
          rlc_finiteTwoChannelConnectorEvent gamma gamma'} :=
      ⟨(split rho.1).1, fun hedge =>
        rho.2 ((rlc_twoChannel_split_fst_mem_event_iff
          gamma gamma' rho.1).mp hedge)⟩
    let sigmaEdge : {omega : RlcTwoChannelEdgeConfig gamma gamma' //
        rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
          rlc_finiteTwoChannelConnectorEvent gamma gamma'} :=
      ⟨(split sigma.1).1, fun hedge =>
        sigma.2 ((rlc_twoChannel_split_fst_mem_event_iff
          gamma gamma' sigma.1).mp hedge)⟩
    change rlc_twoChannelEdgeConfigCombine gamma gamma' (J rhoEdge).1
        (split rho.1).2 =
      rlc_twoChannelEdgeConfigCombine gamma gamma' (J sigmaEdge).1
        (split sigma.1).2 at hrs
    have hsplit := congrArg split hrs
    dsimp only [split] at hsplit
    simp only [rlc_twoChannelEdgeConfigCombine,
      Equiv.apply_symm_apply] at hsplit
    rw [Prod.mk.injEq] at hsplit
    have hedge : rhoEdge = sigmaEdge := J.injective (Subtype.ext hsplit.1)
    apply Subtype.ext
    apply split.injective
    exact Prod.ext (congrArg Subtype.val hedge) hsplit.2

end
end StatMech.Universality
