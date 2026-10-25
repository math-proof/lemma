/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStaticCutEndpoint
import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part16
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelAmbientPermutation.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelIndexedAmbientFailureMap_success
    {n : Int} {I : Type*} (pair : I → RlcDiagonalPathPair n)
    (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
    (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection
      (pair i).1 (pair i).2 (hfaith i))
    (x : RlcTwoChannelIndexedSelectedFailure I pair) :
    rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x ∈
      rlc_finiteTwoChannelConnectorEvent
        (pair x.index).1 (pair x.index).2 := by
  exact rlc_twoChannelFullPhysicalAmbientFailureEmbedding_success
    (hfaith x.index) (hstatic x.index) ⟨x.config, x.failure⟩


theorem rlc_twoChannelIndexedAmbientFailureMap_agreesOff
    {n : Int} {I : Type*} (pair : I → RlcDiagonalPathPair n)
    (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
    (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection
      (pair i).1 (pair i).2 (hfaith i))
    (x : RlcTwoChannelIndexedSelectedFailure I pair) :
    FK.AgreesOff
      (rlc_connectorTwoChannelGraph
        (pair x.index).1 (pair x.index).2).edgeFinset
      x.config
      (rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x) := by
  exact rlc_twoChannelFullPhysicalAmbientFailureEmbedding_agreesOff
    (hfaith x.index) (hstatic x.index) ⟨x.config, x.failure⟩


theorem rlc_twoChannelIndexedAmbientFailureMap_collision_agreesOff_union
    {n : Int} {I : Type*} (pair : I → RlcDiagonalPathPair n)
    (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
    (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection
      (pair i).1 (pair i).2 (hfaith i))
    {x y : RlcTwoChannelIndexedSelectedFailure I pair}
    (hxy : rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x =
      rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic y) :
    ∀ e,
      e ∉ (rlc_connectorTwoChannelGraph
        (pair x.index).1 (pair x.index).2).edgeFinset →
      e ∉ (rlc_connectorTwoChannelGraph
        (pair y.index).1 (pair y.index).2).edgeFinset →
      x.config e = y.config e := by
  intro e hex hey
  calc
    x.config e =
        rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x e :=
      (rlc_twoChannelIndexedAmbientFailureMap_agreesOff
        pair hfaith hstatic x e hex).symm
    _ = rlc_twoChannelIndexedAmbientFailureMap
        pair hfaith hstatic y e := congrFun hxy e
    _ = y.config e :=
      rlc_twoChannelIndexedAmbientFailureMap_agreesOff
        pair hfaith hstatic y e hey


theorem rlc_twoChannelIndexedAmbientFailureMap_trace_open
    {n : Int} {I : Type*} (pair : I → RlcDiagonalPathPair n)
    (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
    (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection
      (pair i).1 (pair i).2 (hfaith i))
    (x : RlcTwoChannelIndexedSelectedFailure I pair) :
    ∀ e ∈ (rlc_connectorTraceWiring
      (pair x.index).1 (pair x.index).2).edgeFinset,
      rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x e = true := by
  intro e heTrace
  have heOutside : e ∉ (rlc_connectorTwoChannelGraph
      (pair x.index).1 (pair x.index).2).edgeFinset := fun heChannel =>
    (Finset.disjoint_left.mp
      (rlc_connectorTwoChannelGraph_edgeFinset_disjoint_traceWiring
        (pair x.index).1 (pair x.index).2)) heChannel heTrace
  rw [rlc_twoChannelIndexedAmbientFailureMap_agreesOff
    pair hfaith hstatic x e heOutside]
  exact rlc_finiteExtremalPairCandidate_trace_open
    (pair x.index).1 (pair x.index).2 x.selected e heTrace


end
end StatMech.Universality
