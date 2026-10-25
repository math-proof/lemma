/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStaticCutEndpoint
import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part16
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelAmbientPermutation.Part5
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_twoChannelIndexedAmbientTargetDiagonalConfig
    {n : Int} {I : Type*} (pair : I → RlcDiagonalPathPair n)
    (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
    (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection
      (pair i).1 (pair i).2 (hfaith i))
    (x : RlcTwoChannelIndexedSelectedFailure I pair) :
    RlcTwoChannelFiniteDiagonalConfig n := by
  let psi := rlc_twoChannelIndexedAmbientFailureMap
    pair hfaith hstatic x
  have hopen : rlc_connectorExtendConfig psi ∈
      rlc_pathPairOpen (pair x.index) :=
    rlc_connectorExtendConfig_pathPairOpen_of_trace_open
      (pair x.index).1 (pair x.index).2 psi
      (rlc_twoChannelIndexedAmbientFailureMap_trace_open
        pair hfaith hstatic x)
  refine ⟨psi, ?_⟩
  constructor
  · rw [← rlc_iUnion_rightDiagonalPath n]
    exact Set.mem_iUnion.mpr ⟨(pair x.index).1, hopen.1⟩
  · rw [← rlc_iUnion_leftDiagonalPath n]
    exact Set.mem_iUnion.mpr ⟨(pair x.index).2, hopen.2⟩


noncomputable def rlc_twoChannelIndexedAmbientTargetSelector
    {n : Int} {I : Type*} (pair : I → RlcDiagonalPathPair n)
    (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
    (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection
      (pair i).1 (pair i).2 (hfaith i))
    (x : RlcTwoChannelIndexedSelectedFailure I pair) :
    RlcTwoChannelActiveFiniteExtremalPair n :=
  rlc_twoChannelFiniteExtremalPairSelector
    (rlc_twoChannelIndexedAmbientTargetDiagonalConfig
      pair hfaith hstatic x)


end
end StatMech.Universality
