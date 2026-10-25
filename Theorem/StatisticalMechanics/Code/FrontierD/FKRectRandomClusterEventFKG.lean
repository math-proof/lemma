/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9


namespace StatMech.FrontierD

noncomputable section

theorem fkRectCriticalEventMass_eq_indicatorExpectation
    (R : FKRectTorus) (q : Real) (A : Set R.Configuration) :
    fkRectCriticalEventMass R q A =
      ∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          A.indicator (fun _ => (1 : Real)) omega := by
  classical
  unfold fkRectCriticalEventMass
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases hA : omega ∈ A <;> simp [Set.indicator, hA]

@[simp] theorem fkRectCriticalEventMass_univ
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    fkRectCriticalEventMass R q Set.univ = 1 := by
  unfold fkRectCriticalEventMass
  simp [sum_fkRectCriticalRandomClusterProb R hq]


theorem fkRectCriticalEventMass_compl_add
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (A : Set R.Configuration) :
    fkRectCriticalEventMass R q Aᶜ + fkRectCriticalEventMass R q A = 1 := by
  classical
  unfold fkRectCriticalEventMass
  rw [← Finset.sum_add_distrib]
  calc
    ∑ omega : R.Configuration,
        (Aᶜ.indicator
            (fun omega => fkRectCriticalRandomClusterProb R q omega) omega +
          A.indicator
            (fun omega => fkRectCriticalRandomClusterProb R q omega) omega) =
        ∑ omega : R.Configuration,
          fkRectCriticalRandomClusterProb R q omega := by
            apply Finset.sum_congr rfl
            intro omega homega
            by_cases hA : omega ∈ A <;> simp [Set.indicator, hA]
    _ = 1 := sum_fkRectCriticalRandomClusterProb R hq

theorem fkRectCriticalEventMass_compl
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (A : Set R.Configuration) :
    fkRectCriticalEventMass R q Aᶜ =
      1 - fkRectCriticalEventMass R q A := by
  linarith [fkRectCriticalEventMass_compl_add R hq A]


theorem fkRectCriticalEventMass_mul_le_inter
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    {A B : Set R.Configuration}
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    fkRectCriticalEventMass R q A * fkRectCriticalEventMass R q B ≤
      fkRectCriticalEventMass R q (A ∩ B) := by
  rw [fkRectCriticalEventMass_eq_indicatorExpectation,
    fkRectCriticalEventMass_eq_indicatorExpectation,
    fkRectCriticalEventMass_eq_indicatorExpectation]
  have hAB : (A ∩ B).indicator (fun _ => (1 : Real)) =
      fun omega =>
        A.indicator (fun _ => (1 : Real)) omega *
          B.indicator (fun _ => (1 : Real)) omega := by
    funext omega
    by_cases ha : omega ∈ A <;> by_cases hb : omega ∈ B <;>
      simp [Set.indicator, ha, hb, Set.mem_inter_iff]
  rw [hAB]
  exact fkRectCritical_positivelyAssociated R hq
    hA.indicator_monotone hB.indicator_monotone


theorem fkRectCriticalEventMass_mul_le_inter_decreasing
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    {A B : Set R.Configuration}
    (hA : IsDecreasing A) (hB : IsDecreasing B) :
    fkRectCriticalEventMass R q A * fkRectCriticalEventMass R q B ≤
      fkRectCriticalEventMass R q (A ∩ B) := by
  let f : R.Configuration -> Real :=
    A.indicator (fun _ => (1 : Real))
  let g : R.Configuration -> Real :=
    B.indicator (fun _ => (1 : Real))
  have hfanti : Antitone f := by
    intro omega tau hot
    by_cases homega : omega ∈ A
    · by_cases htau : tau ∈ A <;> simp [f, homega, htau]
    · have htau : tau ∉ A := fun htau => homega (hA hot htau)
      simp [f, homega, htau]
  have hganti : Antitone g := by
    intro omega tau hot
    by_cases homega : omega ∈ B
    · by_cases htau : tau ∈ B <;> simp [g, homega, htau]
    · have htau : tau ∉ B := fun htau => homega (hB hot htau)
      simp [g, homega, htau]
  have hfmono : Monotone (fun omega => -f omega) := fun _ _ h =>
    neg_le_neg (hfanti h)
  have hgmono : Monotone (fun omega => -g omega) := fun _ _ h =>
    neg_le_neg (hganti h)
  rw [fkRectCriticalEventMass_eq_indicatorExpectation,
    fkRectCriticalEventMass_eq_indicatorExpectation,
    fkRectCriticalEventMass_eq_indicatorExpectation]
  have hAB : (A ∩ B).indicator (fun _ => (1 : Real)) =
      fun omega => f omega * g omega := by
    funext omega
    by_cases ha : omega ∈ A <;> by_cases hb : omega ∈ B <;>
      simp [f, g, Set.indicator, ha, hb, Set.mem_inter_iff]
  rw [hAB]
  simpa only [mul_neg, Finset.sum_neg_distrib, neg_mul, neg_neg] using
    (fkRectCritical_positivelyAssociated R hq hfmono hgmono)


end
end StatMech.FrontierD
