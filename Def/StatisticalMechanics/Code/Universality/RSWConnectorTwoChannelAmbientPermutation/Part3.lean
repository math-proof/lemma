/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStaticCutEndpoint
import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part16
import Structure.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelAmbientPermutation
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_twoChannelIndexedAmbientFailureMap
    {n : Int} {I : Type*} (pair : I → RlcDiagonalPathPair n)
    (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
    (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection
      (pair i).1 (pair i).2 (hfaith i))
    (x : RlcTwoChannelIndexedSelectedFailure I pair) :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  rlc_twoChannelFullPhysicalAmbientFailureEmbedding
    (hfaith x.index) (hstatic x.index) ⟨x.config, x.failure⟩


def RlcTwoChannelIndexedAmbientCollisionRecovery
    {n : Int} {I : Type*} (pair : I → RlcDiagonalPathPair n)
    (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
    (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection
      (pair i).1 (pair i).2 (hfaith i)) : Prop :=
  ∀ x y : RlcTwoChannelIndexedSelectedFailure I pair,
    rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x =
        rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic y →
      x.index = y.index


end
end StatMech.Universality
