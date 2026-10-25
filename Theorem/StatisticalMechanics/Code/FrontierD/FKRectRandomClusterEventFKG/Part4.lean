/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9
import Def.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterEventFKG.Part3


namespace StatMech.FrontierD

noncomputable section

theorem fkRectTorusConnectionChainEvent_isIncreasing
    (R : FKRectTorus) (s : Finset (R.Vertex × R.Vertex)) :
    IsIncreasing (fkRectTorusConnectionChainEvent R s) := by
  apply fkRectFiniteEventIntersection_isIncreasing
  intro p hp
  exact fkRectTorusConnectionEvent_isIncreasing R p.1 p.2


theorem fkRectCriticalEventMass_connectionChain_ge_prod
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (s : Finset (R.Vertex × R.Vertex)) :
    (∏ p ∈ s, fkRectCriticalEventMass R q
        (fkRectTorusConnectionEvent R p.1 p.2)) ≤
      fkRectCriticalEventMass R q
        (fkRectTorusConnectionChainEvent R s) := by
  exact fkRectCriticalEventMass_prod_le_finiteIntersection R hq s
    (fun p => fkRectTorusConnectionEvent R p.1 p.2)
    (fun p _ => fkRectTorusConnectionEvent_isIncreasing R p.1 p.2)


theorem fkRectCriticalEventMass_connectionChain_ge_pow
    (R : FKRectTorus) {q a : Real} (hq : 1 ≤ q) (ha : 0 ≤ a)
    (s : Finset (R.Vertex × R.Vertex))
    (hblock : ∀ p ∈ s, a ≤ fkRectCriticalEventMass R q
      (fkRectTorusConnectionEvent R p.1 p.2)) :
    a ^ s.card ≤ fkRectCriticalEventMass R q
      (fkRectTorusConnectionChainEvent R s) := by
  calc
    a ^ s.card = ∏ _p ∈ s, a := by simp
    _ ≤ ∏ p ∈ s, fkRectCriticalEventMass R q
        (fkRectTorusConnectionEvent R p.1 p.2) := by
      exact Finset.prod_le_prod (fun _ _ => ha) hblock
    _ ≤ fkRectCriticalEventMass R q
        (fkRectTorusConnectionChainEvent R s) :=
      fkRectCriticalEventMass_connectionChain_ge_prod R hq s


theorem fkRectCriticalEventMass_event_mul_connectionChain_le
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (B : Set R.Configuration) (hB : IsIncreasing B)
    (s : Finset (R.Vertex × R.Vertex)) :
    fkRectCriticalEventMass R q B *
        (∏ p ∈ s, fkRectCriticalEventMass R q
          (fkRectTorusConnectionEvent R p.1 p.2)) ≤
      fkRectCriticalEventMass R q
        (B ∩ fkRectTorusConnectionChainEvent R s) := by
  have hchain := fkRectCriticalEventMass_connectionChain_ge_prod R hq s
  have hBnonneg := fkRectCriticalEventMass_nonneg R
    (lt_of_lt_of_le zero_lt_one hq) B
  calc
    _ ≤ fkRectCriticalEventMass R q B *
        fkRectCriticalEventMass R q
          (fkRectTorusConnectionChainEvent R s) :=
      mul_le_mul_of_nonneg_left hchain hBnonneg
    _ ≤ _ := fkRectCriticalEventMass_mul_le_inter R hq hB
      (fkRectTorusConnectionChainEvent_isIncreasing R s)


theorem fkRectCriticalEventMass_event_mul_pow_le_connectionChain
    (R : FKRectTorus) {q a : Real} (hq : 1 ≤ q) (ha : 0 ≤ a)
    (B : Set R.Configuration) (hB : IsIncreasing B)
    (s : Finset (R.Vertex × R.Vertex))
    (hblock : ∀ p ∈ s, a ≤ fkRectCriticalEventMass R q
      (fkRectTorusConnectionEvent R p.1 p.2)) :
    fkRectCriticalEventMass R q B * a ^ s.card ≤
      fkRectCriticalEventMass R q
        (B ∩ fkRectTorusConnectionChainEvent R s) := by
  have hpow := fkRectCriticalEventMass_connectionChain_ge_pow
    R hq ha s hblock
  have hBnonneg := fkRectCriticalEventMass_nonneg R
    (lt_of_lt_of_le zero_lt_one hq) B
  calc
    _ ≤ fkRectCriticalEventMass R q B *
        fkRectCriticalEventMass R q
          (fkRectTorusConnectionChainEvent R s) :=
      mul_le_mul_of_nonneg_left hpow hBnonneg
    _ ≤ _ := fkRectCriticalEventMass_mul_le_inter R hq hB
      (fkRectTorusConnectionChainEvent_isIncreasing R s)


end
end StatMech.FrontierD
