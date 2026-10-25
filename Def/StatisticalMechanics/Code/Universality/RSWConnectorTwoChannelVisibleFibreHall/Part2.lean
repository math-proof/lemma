/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelVisibleFibreHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part43
import Abbrev.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelVisibleFibreHall.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

noncomputable section

def RlcTwoChannelPIMSPooledVisibleFibreCapacity {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma') : Prop :=
  forall base : RlcTwoChannelPIMSVisibleBase gamma gamma',
    Fintype.card (RlcTwoChannelFailureVisibleFibre hclosure base) <=
      Fintype.card (RlcTwoChannelSuccessVisibleFibre base)


def RlcTwoChannelPIMSPooledVisibleCompatible {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (rho : RlcTwoChannelEdgeFailure gamma gamma')
    (eta : RlcTwoChannelEdgeSuccess gamma gamma') : Prop :=
  rlc_twoChannelSuccessVisibleBase eta =
    rlc_twoChannelFailureVisibleBase hclosure rho


def RlcTwoChannelPIMSPooledScoreCompatible {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (N : Nat) (rho : RlcTwoChannelEdgeFailure gamma gamma')
    (eta : RlcTwoChannelEdgeSuccess gamma gamma') : Prop :=
  RlcTwoChannelPIMSPooledVisibleCompatible hclosure rho eta ∧
    FK.openCount (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) +
        2 * FK.numClustersBC
          (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma')
          (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <=
      FK.openCount (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) +
        2 * FK.numClustersBC
          (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) + N

noncomputable def rlc_sigmaEmbedding
    {alpha : Type*} {beta gamma : alpha -> Type*}
    (f : forall a, beta a ↪ gamma a) : (Sigma beta) ↪ Sigma gamma where
  toFun x := ⟨x.1, f x.1 x.2⟩
  inj' := by
    rintro ⟨a, x⟩ ⟨b, y⟩ h
    have hab : a = b := congrArg Sigma.fst h
    subst b
    have hout : f a x = f a y := by
      exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
    have hxy : x = y := (f a).injective hout
    subst y
    rfl

noncomputable def rlc_twoChannelVisibleFibreEmbedding
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (hcapacity : RlcTwoChannelPIMSPooledVisibleFibreCapacity hclosure)
    (base : RlcTwoChannelPIMSVisibleBase gamma gamma') :
    RlcTwoChannelFailureVisibleFibre hclosure base ↪
      RlcTwoChannelSuccessVisibleFibre base :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (hcapacity base))


noncomputable def rlc_twoChannelPooledVisibleEmbeddingOfCapacity
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (hcapacity : RlcTwoChannelPIMSPooledVisibleFibreCapacity hclosure) :
    RlcTwoChannelEdgeFailure gamma gamma' ↪
      RlcTwoChannelEdgeSuccess gamma gamma' :=
  (Equiv.sigmaFiberEquiv
      (rlc_twoChannelFailureVisibleBase hclosure)).symm.toEmbedding |>.trans
    (rlc_sigmaEmbedding fun base =>
      rlc_twoChannelVisibleFibreEmbedding hcapacity base) |>.trans
    (Equiv.sigmaFiberEquiv
      (rlc_twoChannelSuccessVisibleBase
        (gamma := gamma) (gamma' := gamma'))).toEmbedding

end
end StatMech.Universality
