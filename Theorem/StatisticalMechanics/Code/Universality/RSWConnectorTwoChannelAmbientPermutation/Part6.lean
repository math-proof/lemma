/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStaticCutEndpoint
import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part16
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelAmbientPermutation.Part4
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelActiveAmbientTargetSelector_eq_iff_stable
    {n : Int} (hright : RlcRightEnvelopeProperty n)
    (hleft : RlcLeftEnvelopeProperty n)
    (hfaith : ∀ i : RlcTwoChannelActiveFiniteExtremalPair n,
      RlcBookFaithfulTracePair i.1.1 i.1.2)
    (hstatic : ∀ i : RlcTwoChannelActiveFiniteExtremalPair n,
      RlcTwoChannelFullPhysicalStaticCutIntersection
        i.1.1 i.1.2 (hfaith i))
    (x : RlcTwoChannelIndexedSelectedFailure
      (RlcTwoChannelActiveFiniteExtremalPair n) Subtype.val) :
    rlc_twoChannelIndexedAmbientTargetSelector
        Subtype.val hfaith hstatic x = x.index ↔
      rlc_twoChannelIndexedAmbientFailureMap
          Subtype.val hfaith hstatic x ∈
        rlc_finiteExtremalPairCandidate
          x.index.1.1 x.index.1.2 := by
  constructor
  · intro heq
    have hselected := rlc_twoChannelFiniteExtremalPairSelector_selected
      (rlc_twoChannelIndexedAmbientTargetDiagonalConfig
        Subtype.val hfaith hstatic x)
    change rlc_twoChannelFiniteExtremalPairSelector
      (rlc_twoChannelIndexedAmbientTargetDiagonalConfig
        Subtype.val hfaith hstatic x) = x.index at heq
    change rlc_twoChannelIndexedAmbientFailureMap
        Subtype.val hfaith hstatic x ∈
      rlc_finiteExtremalPairCandidate
        (rlc_twoChannelFiniteExtremalPairSelector
          (rlc_twoChannelIndexedAmbientTargetDiagonalConfig
            Subtype.val hfaith hstatic x)).1.1
        (rlc_twoChannelFiniteExtremalPairSelector
          (rlc_twoChannelIndexedAmbientTargetDiagonalConfig
            Subtype.val hfaith hstatic x)).1.2 at hselected
    rwa [heq] at hselected
  · intro hstable
    apply rlc_twoChannelFiniteExtremalPairSelector_eq_of_selected
      hright hleft
    exact hstable


theorem rlc_twoChannelIndexedAmbientFailureMap_glues_horizontal
    {n : Int} (hn : 0 < n) {I : Type*}
    (pair : I → RlcDiagonalPathPair n)
    (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
    (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection
      (pair i).1 (pair i).2 (hfaith i))
    (x : RlcTwoChannelIndexedSelectedFailure I pair) :
    rlc_connectorExtendConfig
        (rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x) ∈
      horizontalCrossingEvent (-2 * n) (2 * n) (-n) n := by
  apply rlc_twoChannelConnector_glues_horizontal n hn
    (pair x.index).1 (pair x.index).2
  refine ⟨rlc_connectorExtendConfig_pathPairOpen_of_trace_open
    (pair x.index).1 (pair x.index).2 _
      (rlc_twoChannelIndexedAmbientFailureMap_trace_open
        pair hfaith hstatic x), ?_⟩
  change rlc_connectorRestrictConfig
      (rlc_connectorExtendConfig
        (rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x)) ∈
    rlc_finiteTwoChannelConnectorEvent
      (pair x.index).1 (pair x.index).2
  have hrestrict : rlc_connectorRestrictConfig
      (rlc_connectorExtendConfig
        (rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x)) =
      rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x := by
    funext e
    exact rlc_connectorExtendConfig_apply _ e
  rw [hrestrict]
  exact rlc_twoChannelIndexedAmbientFailureMap_success
    pair hfaith hstatic x


theorem rlc_twoChannelIndexedAmbientCollisionRecovery_of_target_stable
    {n : Int} {I : Type*} (pair : I → RlcDiagonalPathPair n)
    (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
    (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection
      (pair i).1 (pair i).2 (hfaith i))
    (hdisjoint : Pairwise fun i j : I ↦
      Disjoint
        (rlc_finiteExtremalPairCandidate (pair i).1 (pair i).2)
        (rlc_finiteExtremalPairCandidate (pair j).1 (pair j).2))
    (hstable : ∀ x : RlcTwoChannelIndexedSelectedFailure I pair,
      rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x ∈
        rlc_finiteExtremalPairCandidate
          (pair x.index).1 (pair x.index).2) :
    RlcTwoChannelIndexedAmbientCollisionRecovery pair hfaith hstatic := by
  intro x y hxy
  by_contra hne
  exact Set.disjoint_left.mp (hdisjoint hne)
    (hstable x) (hxy ▸ hstable y)


theorem
    rlc_twoChannelActiveAmbientCollisionRecovery_of_target_stable
    {n : Int} (hright : RlcRightEnvelopeProperty n)
    (hleft : RlcLeftEnvelopeProperty n)
    (hfaith : ∀ i : RlcTwoChannelActiveFiniteExtremalPair n,
      RlcBookFaithfulTracePair i.1.1 i.1.2)
    (hstatic : ∀ i : RlcTwoChannelActiveFiniteExtremalPair n,
      RlcTwoChannelFullPhysicalStaticCutIntersection
        i.1.1 i.1.2 (hfaith i))
    (hstable : ∀ x : RlcTwoChannelIndexedSelectedFailure
        (RlcTwoChannelActiveFiniteExtremalPair n) Subtype.val,
      rlc_twoChannelIndexedAmbientFailureMap
          Subtype.val hfaith hstatic x ∈
        rlc_finiteExtremalPairCandidate
          x.index.1.1 x.index.1.2) :
    RlcTwoChannelIndexedAmbientCollisionRecovery
      Subtype.val hfaith hstatic := by
  apply rlc_twoChannelIndexedAmbientCollisionRecovery_of_target_stable
    Subtype.val hfaith hstatic
    (rlc_activeFiniteExtremalPairCandidate_pairwiseDisjoint hright hleft)
    hstable


theorem rlc_twoChannelIndexedAmbientCollisionRecovery_const_bool_no_go
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hfaith)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hselected : rho ∈ rlc_finiteExtremalPairCandidate gamma gamma')
    (hfailure : rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    ¬ RlcTwoChannelIndexedAmbientCollisionRecovery
      (I := Bool) (fun _ ↦ (gamma, gamma')) (fun _ ↦ hfaith)
        (fun _ ↦ hstatic) := by
  intro hrecover
  let x : RlcTwoChannelIndexedSelectedFailure Bool
      (fun _ ↦ (gamma, gamma')) :=
    ⟨false, rho, hselected, hfailure⟩
  let y : RlcTwoChannelIndexedSelectedFailure Bool
      (fun _ ↦ (gamma, gamma')) :=
    ⟨true, rho, hselected, hfailure⟩
  have hmap : rlc_twoChannelIndexedAmbientFailureMap
      (fun _ : Bool ↦ (gamma, gamma')) (fun _ ↦ hfaith)
        (fun _ ↦ hstatic) x =
      rlc_twoChannelIndexedAmbientFailureMap
        (fun _ : Bool ↦ (gamma, gamma')) (fun _ ↦ hfaith)
          (fun _ ↦ hstatic) y := rfl
  have := hrecover x y hmap
  simp [x, y] at this


end
end StatMech.Universality
