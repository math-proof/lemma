/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterMatchingCutCurrent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoGhostVarianceSector
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterMatchingCutCurrent.Part3
open Finset
open scoped BigOperators symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {W I : Type*} [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I]


theorem lpMatchingFiveCurrentCoefficient_commonSource
    (Si Sj T : Finset W) :
    lpFiveSourceTotal (Si ∆ Sj ∆ T) ∅ ∅ ∅ ∅ = Si ∆ Sj ∆ T ∧
    lpFiveSourceTotal (Si ∆ Sj) T ∅ ∅ ∅ = Si ∆ Sj ∆ T ∧
    lpFiveSourceTotal Si (Sj ∆ T) ∅ ∅ ∅ = Si ∆ Sj ∆ T ∧
    lpFiveSourceTotal Si Sj T ∅ ∅ = Si ∆ Sj ∆ T ∧
    lpFiveSourceTotal (Si ∆ Sj ∆ T) T T ∅ ∅ = Si ∆ Sj ∆ T ∧
    lpFiveSourceTotal (Si ∆ Sj) T T T ∅ = Si ∆ Sj ∆ T ∧
    lpFiveSourceTotal Si (Sj ∆ T) T T ∅ = Si ∆ Sj ∆ T ∧
    lpFiveSourceTotal (Si ∆ T) (Sj ∆ T) T ∅ ∅ = Si ∆ Sj ∆ T := by
  constructor
  · ext x
    simp [lpFiveSourceTotal, Finset.mem_symmDiff]
  constructor
  · ext x
    simp [lpFiveSourceTotal, Finset.mem_symmDiff]
  constructor
  · ext x
    simp [lpFiveSourceTotal, Finset.mem_symmDiff]
    tauto
  constructor
  · ext x
    simp [lpFiveSourceTotal, Finset.mem_symmDiff]
  constructor
  · ext x
    simp [lpFiveSourceTotal, Finset.mem_symmDiff]
  constructor
  · ext x
    simp [lpFiveSourceTotal, Finset.mem_symmDiff]
  constructor
  · ext x
    simp [lpFiveSourceTotal, Finset.mem_symmDiff]
    tauto
  · ext x
    simp [lpFiveSourceTotal, Finset.mem_symmDiff]
    tauto


theorem lpMatchingCurrentSkewPolynomial_eq_sum_fiveCurrentCoefficient
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) :
    lpMatchingCurrentSkewPolynomial
        (lpMatchingCurrentA G beta J left right)
        (lpMatchingCurrentB G beta J left right g0 g1)
        (lpMatchingCurrentC G beta J g0 g1)
        (lpMatchingCurrentD G beta J left right)
        (lpMatchingCurrentE G beta J left right g0 g1)
        (lpMatchingCurrentZ G beta J) =
      ∑ i : I, ∑ j : I,
        lpMatchingFiveCurrentCoefficient G beta J left right g0 g1 i j := by
  rw [lpMatchingCurrentSkewPolynomial_expanded]
  unfold lpMatchingCurrentA lpMatchingCurrentB lpMatchingCurrentC
    lpMatchingCurrentD lpMatchingCurrentE lpMatchingCurrentZ
    lpMatchingFiveCurrentCoefficient lpFiveCurrentSourceMass
  simp only [pow_two, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]
  ring


theorem lpMatching_centeredGhostCovariance_eq_currentPolynomial
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) :
    let a := ∑ i : I,
      expectationJ G beta J (lpMatchingSeamSource left right i)
    let b := ∑ i : I, expectationJ G beta J
      (lpMatchingSeamSource left right i ∆ lpMatchingGhostSource g0 g1)
    let c := expectationJ G beta J (lpMatchingGhostSource g0 g1)
    let d := ∑ i : I, ∑ j : I, expectationJ G beta J
      (lpMatchingSeamSource left right i ∆ lpMatchingSeamSource left right j)
    let e := ∑ i : I, ∑ j : I, expectationJ G beta J
      (lpMatchingSeamSource left right i ∆
        lpMatchingSeamSource left right j ∆ lpMatchingGhostSource g0 g1)
    let A := lpMatchingCurrentA G beta J left right
    let B := lpMatchingCurrentB G beta J left right g0 g1
    let C := lpMatchingCurrentC G beta J g0 g1
    let D := lpMatchingCurrentD G beta J left right
    let E := lpMatchingCurrentE G beta J left right g0 g1
    let Z := lpMatchingCurrentZ G beta J
    (1 - c ^ 2) * ((e - d * c) - 2 * a * (b - a * c)) +
        2 * c * (b - a * c) ^ 2 =
      lpMatchingCurrentSkewPolynomial A B C D E Z / Z ^ 5 := by
  dsimp only
  let Z := currentSum G beta J ∅
  have hZ : Ne Z 0 := ne_of_gt (acr_currentSum_empty_pos G beta J)
  have ha : (∑ i : I,
      expectationJ G beta J (lpMatchingSeamSource left right i)) =
      lpMatchingCurrentA G beta J left right / Z := by
    simp_rw [current_representation]
    unfold lpMatchingCurrentA
    rw [sum_div]
  have hb : (∑ i : I, expectationJ G beta J
      (lpMatchingSeamSource left right i ∆ lpMatchingGhostSource g0 g1)) =
      lpMatchingCurrentB G beta J left right g0 g1 / Z := by
    simp_rw [current_representation]
    unfold lpMatchingCurrentB
    rw [sum_div]
  have hc : expectationJ G beta J (lpMatchingGhostSource g0 g1) =
      lpMatchingCurrentC G beta J g0 g1 / Z := by
    rw [current_representation]
    unfold lpMatchingCurrentC
    rfl
  have hd : (∑ i : I, ∑ j : I, expectationJ G beta J
      (lpMatchingSeamSource left right i ∆ lpMatchingSeamSource left right j)) =
      lpMatchingCurrentD G beta J left right / Z := by
    simp_rw [current_representation]
    unfold lpMatchingCurrentD
    rw [sum_div]
    congr 1
    funext i
    rw [sum_div]
  have he : (∑ i : I, ∑ j : I, expectationJ G beta J
      (lpMatchingSeamSource left right i ∆
        lpMatchingSeamSource left right j ∆ lpMatchingGhostSource g0 g1)) =
      lpMatchingCurrentE G beta J left right g0 g1 / Z := by
    simp_rw [current_representation]
    unfold lpMatchingCurrentE
    rw [sum_div]
    congr 1
    funext i
    rw [sum_div]
  rw [ha, hb, hc, hd, he]
  exact lpTwoGhost_centeredCovariance_clear_current
    (lpMatchingCurrentA G beta J left right)
    (lpMatchingCurrentB G beta J left right g0 g1)
    (lpMatchingCurrentC G beta J g0 g1)
    (lpMatchingCurrentD G beta J left right)
    (lpMatchingCurrentE G beta J left right g0 g1) Z hZ

end
end StatMech.Ising
