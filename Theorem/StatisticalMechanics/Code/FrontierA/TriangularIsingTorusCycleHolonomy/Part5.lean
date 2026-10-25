/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSurfaceTwist
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleHolonomy.Part5
open scoped BigOperators


namespace StatMech.FrontierA

open scoped Affine


theorem triangularTorusTurnExponent_cast_eq_angleClass_sub
    (a b : Fin 6)
    (hne : b ≠ triangularTorusDirectionReverse a) :
    (triangularTorusTurnExponent a b : ZMod 8) =
      triangularTorusDirectionAngleClass b -
        triangularTorusDirectionAngleClass a := by
  fin_cases a <;> fin_cases b <;>
    simp [triangularTorusDirectionReverse,
      triangularTorusTurnExponent,
      triangularTorusDirectionAngleClass] at hne ⊢ <;>
    decide


theorem exists_triangularTorusTurnExponent_sum_eq_eight_mul
    {n : Nat} [NeZero n] (direction : Fin n -> Fin 6)
    (hnonbacktracking : forall k,
      direction (k + 1) ≠
        triangularTorusDirectionReverse (direction k)) :
    ∃ m : Int,
      (∑ k, triangularTorusTurnExponent
        (direction k) (direction (k + 1))) = 8 * m := by
  have hshift :
      (∑ k, triangularTorusDirectionAngleClass (direction (k + 1))) =
        ∑ k, triangularTorusDirectionAngleClass (direction k) := by
    exact Equiv.sum_comp (Equiv.addRight (1 : Fin n))
      (fun k => triangularTorusDirectionAngleClass (direction k))
  have hcastSum :
      (∑ k, (triangularTorusTurnExponent
        (direction k) (direction (k + 1)) : ZMod 8)) = 0 := by
    rw [show (∑ k, (triangularTorusTurnExponent
        (direction k) (direction (k + 1)) : ZMod 8)) =
        ∑ k, (triangularTorusDirectionAngleClass (direction (k + 1)) -
          triangularTorusDirectionAngleClass (direction k)) by
      apply Finset.sum_congr rfl
      intro k _
      exact triangularTorusTurnExponent_cast_eq_angleClass_sub _ _
        (hnonbacktracking k)]
    rw [Finset.sum_sub_distrib, hshift, sub_self]
  have hmap := map_sum (Int.castAddHom (ZMod 8))
    (fun k : Fin n => triangularTorusTurnExponent
      (direction k) (direction (k + 1))) Finset.univ
  have hcast : (Int.castAddHom (ZMod 8))
      (∑ k, triangularTorusTurnExponent
        (direction k) (direction (k + 1))) = 0 :=
    hmap.trans hcastSum
  have hdvd : (8 : Int) ∣ ∑ k, triangularTorusTurnExponent
      (direction k) (direction (k + 1)) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp hcast
  rcases hdvd with ⟨m, hm⟩
  exact ⟨m, hm⟩


theorem exists_triangularTorus_cycleTurnSum_eq_eight_mul
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    ∃ m : Int,
      (∑ k, triangularTorusTurnExponent
        (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k))
        (triangularTorusGraphDartDirection L
          (kwGraphCycleDartLoop p (k + 1)))) = 8 * m := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  exact exists_triangularTorusTurnExponent_sum_eq_eight_mul _
    (triangularTorus_cycleDirection_nonbacktracking L p hp)

theorem triangularTorusTurnRoot_pow_eight
    (rho : Complex) (hrho : rho ^ 4 = Complex.I) :
    rho ^ 8 = -1 := by
  calc
    rho ^ 8 = (rho ^ 4) ^ 2 := by ring
    _ = Complex.I ^ 2 := by rw [hrho]
    _ = -1 := by norm_num

theorem triangularTorusTurnRoot_ne_zero
    (rho : Complex) (hrho : rho ^ 4 = Complex.I) : rho ≠ 0 := by
  intro hz
  rw [hz] at hrho
  have hzero : (0 : Complex) ^ 4 = 0 := by norm_num
  rw [hzero] at hrho
  exact Complex.I_ne_zero hrho.symm


theorem triangularKacWardTurnMatrix_eq_zpow
    (rho : Complex) (hrho : rho ^ 4 = Complex.I) (a b : Fin 6)
    (hne : b ≠ triangularTorusDirectionReverse a) :
    triangularKacWardTurnMatrix rho a b =
      rho ^ triangularTorusTurnExponent a b := by
  have hrho0 := triangularTorusTurnRoot_ne_zero rho hrho
  have hrho8 := triangularTorusTurnRoot_pow_eight rho hrho
  fin_cases a <;> fin_cases b <;>
    simp [triangularTorusDirectionReverse, triangularTorusTurnExponent,
      triangularKacWardTurnMatrix] at hne ⊢ <;>
    field_simp <;>
    rw [hrho8] <;> norm_num


theorem prod_triangularKacWardTurnMatrix_eq_zpow_sum
    {n : Nat} [NeZero n]
    (rho : Complex) (hrho : rho ^ 4 = Complex.I)
    (direction : Fin n -> Fin 6)
    (hnonbacktracking : forall k,
      direction (k + 1) ≠
        triangularTorusDirectionReverse (direction k)) :
    (∏ k, triangularKacWardTurnMatrix rho
        (direction k) (direction (k + 1))) =
      rho ^ (∑ k, triangularTorusTurnExponent
        (direction k) (direction (k + 1))) := by
  rw [show (∏ k, triangularKacWardTurnMatrix rho
      (direction k) (direction (k + 1))) =
      ∏ k, rho ^ triangularTorusTurnExponent
        (direction k) (direction (k + 1)) by
    apply Finset.prod_congr rfl
    intro k _
    exact triangularKacWardTurnMatrix_eq_zpow rho hrho _ _
      (hnonbacktracking k)]
  exact StatMech.Onsager.ons_prod_zpow rho
    (triangularTorusTurnRoot_ne_zero rho hrho) _ _


theorem triangularTorusTurnRoot_zpow_even_revolutions
    (rho : Complex) (hrho : rho ^ 4 = Complex.I) (m : Int) :
    rho ^ (8 * (2 * m)) = 1 := by
  have hrho8 : rho ^ (8 : Int) = -1 := by
    simpa [zpow_ofNat] using
      triangularTorusTurnRoot_pow_eight rho hrho
  rw [_root_.zpow_mul, _root_.zpow_mul]
  rw [hrho8]
  norm_num


theorem triangularTorusTurnRoot_zpow_odd_revolutions
    (rho : Complex) (hrho : rho ^ 4 = Complex.I) (m : Int) :
    rho ^ (8 * (2 * m + 1)) = -1 := by
  have hrho8 : rho ^ (8 : Int) = -1 := by
    simpa [zpow_ofNat] using
      triangularTorusTurnRoot_pow_eight rho hrho
  rw [_root_.zpow_mul, zpow_add₀]
  · rw [_root_.zpow_mul]
    rw [hrho8]
    norm_num
  · exact pow_ne_zero 8 (triangularTorusTurnRoot_ne_zero rho hrho)


theorem prod_triangularKacWardTurnMatrix_eq_one_of_even_revolutions
    {n : Nat} [NeZero n]
    (rho : Complex) (hrho : rho ^ 4 = Complex.I)
    (direction : Fin n -> Fin 6)
    (hnonbacktracking : forall k,
      direction (k + 1) ≠
        triangularTorusDirectionReverse (direction k))
    (m : Int)
    (hturn : (∑ k, triangularTorusTurnExponent
      (direction k) (direction (k + 1))) = 8 * (2 * m)) :
    (∏ k, triangularKacWardTurnMatrix rho
        (direction k) (direction (k + 1))) = 1 := by
  rw [prod_triangularKacWardTurnMatrix_eq_zpow_sum rho hrho direction
    hnonbacktracking, hturn]
  exact triangularTorusTurnRoot_zpow_even_revolutions rho hrho m


theorem prod_triangularKacWardTurnMatrix_eq_neg_one_of_odd_revolutions
    {n : Nat} [NeZero n]
    (rho : Complex) (hrho : rho ^ 4 = Complex.I)
    (direction : Fin n -> Fin 6)
    (hnonbacktracking : forall k,
      direction (k + 1) ≠
        triangularTorusDirectionReverse (direction k))
    (m : Int)
    (hturn : (∑ k, triangularTorusTurnExponent
      (direction k) (direction (k + 1))) = 8 * (2 * m + 1)) :
    (∏ k, triangularKacWardTurnMatrix rho
        (direction k) (direction (k + 1))) = -1 := by
  rw [prod_triangularKacWardTurnMatrix_eq_zpow_sum rho hrho direction
    hnonbacktracking, hturn]
  exact triangularTorusTurnRoot_zpow_odd_revolutions rho hrho m


theorem triangularTorus_cyclePhaseProduct_eq_one_of_even_revolutions
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle)
    [NeZero p.darts.length]
    (m : Int)
    (hturn : (∑ k, triangularTorusTurnExponent
      (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k))
      (triangularTorusGraphDartDirection L
        (kwGraphCycleDartLoop p (k + 1)))) = 8 * (2 * m)) :
    kwLoopPhaseProduct (triangularTorusGraphPhase L rho 1 1)
      (kwGraphCycleDartLoop p) = 1 := by
  rw [triangularTorus_cyclePhaseProduct_eq_turnProduct L rho p hp]
  exact prod_triangularKacWardTurnMatrix_eq_one_of_even_revolutions
    rho hrho _ (triangularTorus_cycleDirection_nonbacktracking L p hp) m hturn


theorem triangularTorus_cyclePhaseProduct_eq_neg_one_of_odd_revolutions
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle)
    [NeZero p.darts.length]
    (m : Int)
    (hturn : (∑ k, triangularTorusTurnExponent
      (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k))
      (triangularTorusGraphDartDirection L
        (kwGraphCycleDartLoop p (k + 1)))) = 8 * (2 * m + 1)) :
    kwLoopPhaseProduct (triangularTorusGraphPhase L rho 1 1)
      (kwGraphCycleDartLoop p) = -1 := by
  rw [triangularTorus_cyclePhaseProduct_eq_turnProduct L rho p hp]
  exact prod_triangularKacWardTurnMatrix_eq_neg_one_of_odd_revolutions
    rho hrho _ (triangularTorus_cycleDirection_nonbacktracking L p hp) m hturn

end StatMech.FrontierA
