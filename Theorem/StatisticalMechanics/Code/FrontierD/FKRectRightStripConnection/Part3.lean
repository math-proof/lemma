/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightStripConnection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectInducedConditionalLower.Part3
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectRightStripConnection.Part3


namespace StatMech.FrontierD

noncomputable section

theorem fkRectInducedConnectionChainEvent_isIncreasing
    (R : FKRectTorus) (S : Set R.Vertex)
    (t : Finset (FKRectInducedVertex R S × FKRectInducedVertex R S)) :
    IsIncreasing (fkRectInducedConnectionChainEvent R S t) := by
  intro omega tau hot hmem p hp
  exact FK.connEvent_isIncreasing (fkRectInducedGraph R S) p.1 p.2
    hot (hmem p hp)


theorem fkRectInduced_connectionChain_ge_prod
    (R : FKRectTorus) (S : Set R.Vertex)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (t : Finset (FKRectInducedVertex R S × FKRectInducedVertex R S)) :
    (∏ xy ∈ t,
        FK.twoPointFun (fkRectInducedGraph R S) p q xy.1 xy.2) ≤
      ∑ omega,
        FK.fkProb (fkRectInducedGraph R S) p q omega *
          (fkRectInducedConnectionChainEvent R S t).indicator
            (fun _ => (1 : Real)) omega := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp [fkRectInducedConnectionChainEvent,
        FK.fkProb_sum_eq_one (fkRectInducedGraph R S) hp hp1
          (lt_of_lt_of_le zero_lt_one hq)]
  | @insert xy t hxy ih =>
      have hconn : IsIncreasing
          (FK.connEvent (fkRectInducedGraph R S) xy.1 xy.2) :=
        FK.connEvent_isIncreasing _ _ _
      have hchain : IsIncreasing
          (fkRectInducedConnectionChainEvent R S t) :=
        fkRectInducedConnectionChainEvent_isIncreasing R S t
      have hnonneg : 0 ≤
          FK.twoPointFun (fkRectInducedGraph R S) p q xy.1 xy.2 :=
        FK.twoPointFun_nonneg (fkRectInducedGraph R S) hp hp1
          (lt_of_lt_of_le zero_lt_one hq) _ _
      calc
        (∏ z ∈ insert xy t,
            FK.twoPointFun (fkRectInducedGraph R S) p q z.1 z.2) =
            FK.twoPointFun (fkRectInducedGraph R S) p q xy.1 xy.2 *
              ∏ z ∈ t,
                FK.twoPointFun (fkRectInducedGraph R S) p q z.1 z.2 := by
          rw [Finset.prod_insert hxy]
        _ ≤ FK.twoPointFun (fkRectInducedGraph R S) p q xy.1 xy.2 *
              ∑ omega,
                FK.fkProb (fkRectInducedGraph R S) p q omega *
                  (fkRectInducedConnectionChainEvent R S t).indicator
                    (fun _ => (1 : Real)) omega :=
          mul_le_mul_of_nonneg_left ih hnonneg
        _ ≤ ∑ omega,
              FK.fkProb (fkRectInducedGraph R S) p q omega *
                (FK.connEvent (fkRectInducedGraph R S) xy.1 xy.2 ∩
                  fkRectInducedConnectionChainEvent R S t).indicator
                    (fun _ => (1 : Real)) omega := by
          exact FK.fkProb_positively_associated_events
            (fkRectInducedGraph R S) hp hp1 hq hconn hchain
        _ = ∑ omega,
              FK.fkProb (fkRectInducedGraph R S) p q omega *
                (fkRectInducedConnectionChainEvent R S
                  (insert xy t)).indicator
                    (fun _ => (1 : Real)) omega := by
          apply Finset.sum_congr rfl
          intro omega _
          congr 1
          congr 1
          ext
          simp [fkRectInducedConnectionChainEvent, hxy]


theorem fkRectInduced_connectionProduct_mul_outsideMass_le_genericInter
    (R : FKRectTorus) (S : Set R.Vertex)
    {q : Real} (hq : 1 ≤ q)
    (t : Finset (FKRectInducedVertex R S × FKRectInducedVertex R S))
    {B : Set R.Configuration}
    (hB : FKRectDependsOnOutsideRegion R S B) :
    (∏ xy ∈ t,
        FK.twoPointFun (fkRectInducedGraph R S)
          (fkRectCriticalP q) q xy.1 xy.2) *
        fkRectCriticalEventMass R q B ≤
      ∑ rho,
        ((FK.ocd_innerRestrict
            (Subtype.val : FKRectInducedVertex R S → R.Vertex) ⁻¹'
              fkRectInducedConnectionChainEvent R S t) ∩
          fkRectFullGraphEvent R B).indicator
            (fun _ => (1 : Real)) rho *
          FK.fkProb (fkRectTorusGraph R)
            (fkRectCriticalP q) q rho := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hp := fkRectCriticalP_pos hq0
  have hp1 := fkRectCriticalP_lt_one hq0
  have hprod := fkRectInduced_connectionChain_ge_prod R
    S hp hp1 hq t
  have hBnonneg := fkRectCriticalEventMass_nonneg R hq0 B
  have hlower :=
    fkRectInduced_freeMass_mul_indexedOutsideMass_le_genericInter R
      S hq
      (fkRectInducedConnectionChainEvent_isIncreasing R
        S t) hB
  have hmass :
      (∑ omega,
          FK.fkProb (fkRectInducedGraph R S)
              (fkRectCriticalP q) q omega *
            (fkRectInducedConnectionChainEvent R S t).indicator
                (fun _ => (1 : Real)) omega) =
        ∑ omega,
          (fkRectInducedConnectionChainEvent R S t).indicator
                (fun _ => (1 : Real)) omega *
            FK.fkProb (fkRectInducedGraph R S)
              (fkRectCriticalP q) q omega := by
    apply Finset.sum_congr rfl
    intro omega _
    ring
  calc
    _ ≤ (∑ omega,
          FK.fkProb (fkRectInducedGraph R S)
              (fkRectCriticalP q) q omega *
            (fkRectInducedConnectionChainEvent R S t).indicator
                (fun _ => (1 : Real)) omega) *
          fkRectCriticalEventMass R q B :=
      mul_le_mul_of_nonneg_right hprod hBnonneg
    _ = (∑ omega,
          (fkRectInducedConnectionChainEvent R S t).indicator
                (fun _ => (1 : Real)) omega *
            FK.fkProb (fkRectInducedGraph R S)
              (fkRectCriticalP q) q omega) *
          fkRectCriticalEventMass R q B := by rw [hmass]
    _ ≤ _ := hlower


theorem fkRectRightStrip_connectionProduct_mul_outsideMass_le_genericInter
    (R : FKRectTorus) (cut : Nat)
    {q : Real} (hq : 1 ≤ q)
    (t : Finset (FKRectRightStripVertex R cut ×
      FKRectRightStripVertex R cut))
    {B : Set R.Configuration}
    (hB : FKRectDependsOnOutsideRegion R (fkRectRightStrip R cut) B) :
    (∏ xy ∈ t,
        FK.twoPointFun
          (fkRectInducedGraph R (fkRectRightStrip R cut))
          (fkRectCriticalP q) q xy.1 xy.2) *
        fkRectCriticalEventMass R q B ≤
      ∑ rho,
        ((FK.ocd_innerRestrict
            (Subtype.val : FKRectRightStripVertex R cut → R.Vertex) ⁻¹'
              fkRectInducedConnectionChainEvent R
                (fkRectRightStrip R cut) t) ∩
          fkRectFullGraphEvent R B).indicator
            (fun _ => (1 : Real)) rho *
          FK.fkProb (fkRectTorusGraph R)
            (fkRectCriticalP q) q rho :=
  fkRectInduced_connectionProduct_mul_outsideMass_le_genericInter R
    (fkRectRightStrip R cut) hq t hB


theorem fkRectRightStripBand_connectionProduct_mul_outsideMass_le_genericInter
    (R : FKRectTorus) (cut lower upper : Nat)
    {q : Real} (hq : 1 ≤ q)
    (t : Finset (FKRectRightStripBandVertex R cut lower upper ×
      FKRectRightStripBandVertex R cut lower upper))
    {B : Set R.Configuration}
    (hB : FKRectDependsOnOutsideRegion R
      (fkRectRightStripBand R cut lower upper) B) :
    (∏ xy ∈ t,
        FK.twoPointFun
          (fkRectInducedGraph R
            (fkRectRightStripBand R cut lower upper))
          (fkRectCriticalP q) q xy.1 xy.2) *
        fkRectCriticalEventMass R q B ≤
      ∑ rho,
        ((FK.ocd_innerRestrict
            (Subtype.val :
              FKRectRightStripBandVertex R cut lower upper → R.Vertex) ⁻¹'
              fkRectInducedConnectionChainEvent R
                (fkRectRightStripBand R cut lower upper) t) ∩
          fkRectFullGraphEvent R B).indicator
            (fun _ => (1 : Real)) rho *
          FK.fkProb (fkRectTorusGraph R)
            (fkRectCriticalP q) q rho :=
  fkRectInduced_connectionProduct_mul_outsideMass_le_genericInter R
    (fkRectRightStripBand R cut lower upper) hq t hB

end
end StatMech.FrontierD
