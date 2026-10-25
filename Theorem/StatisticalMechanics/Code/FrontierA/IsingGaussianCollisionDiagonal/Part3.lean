/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCollisionDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalSummation.Part5
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianCollisionDiagonal.Part3
open Filter Finset Set Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem finiteCollisionIntegratedFourthCumulant_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (chi : Real) (hchi : 0 ≤ chi)
    (hrow : ∀ y : V,
      ∑ x : V, expectationJ G beta J (grahamPairSupport x y) ≤ chi)
    (i : V) :
    0 ≤ finiteCollisionIntegratedFourthCumulant G beta J i ∧
      finiteCollisionIntegratedFourthCumulant G beta J i ≤ 12 * chi ^ 2 := by
  let C : V → V → Real := fun x y =>
    expectationJ G beta J (grahamPairSupport x y)
  have hC (x y : V) : 0 ≤ C x y :=
    pairCorrelation_nonneg G beta J hbeta hJ x y
  have hsymm (x y : V) : C x y = C y x := by
    exact pairCorrelation_comm G beta J x y
  have hrow' (y : V) : ∑ x : V, C y x ≤ chi := by
    calc
      ∑ x : V, C y x = ∑ x : V, C x y := by
        apply Finset.sum_congr rfl
        intro x _
        exact hsymm y x
      _ ≤ chi := hrow y
  let A1 := ∑ j : V, ∑ k : V, ∑ l : V,
    if i = j then C i k * C i l else 0
  let A2 := ∑ j : V, ∑ k : V, ∑ l : V,
    if i = k then C i j * C i l else 0
  let A3 := ∑ j : V, ∑ k : V, ∑ l : V,
    if i = l then C i j * C i k else 0
  let A4 := ∑ j : V, ∑ k : V, ∑ l : V,
    if j = k then C j i * C j l else 0
  let A5 := ∑ j : V, ∑ k : V, ∑ l : V,
    if j = l then C j i * C j k else 0
  let A6 := ∑ j : V, ∑ k : V, ∑ l : V,
    if k = l then C k i * C k j else 0
  have hA1 : A1 ≤ chi ^ 2 := by
    dsimp [A1]
    calc
      _ = (∑ k : V, C i k) * (∑ l : V, C i l) := by
        simp [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ ≤ chi * chi := mul_le_mul (hrow' i) (hrow' i)
        (Finset.sum_nonneg fun x _ => hC i x) hchi
      _ = chi ^ 2 := by ring
  have hA2 : A2 ≤ chi ^ 2 := by
    dsimp [A2]
    calc
      _ = (∑ j : V, C i j) * (∑ l : V, C i l) := by
        simp [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ ≤ chi * chi := mul_le_mul (hrow' i) (hrow' i)
        (Finset.sum_nonneg fun x _ => hC i x) hchi
      _ = chi ^ 2 := by ring
  have hA3 : A3 ≤ chi ^ 2 := by
    dsimp [A3]
    calc
      _ = (∑ j : V, C i j) * (∑ k : V, C i k) := by
        simp [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ ≤ chi * chi := mul_le_mul (hrow' i) (hrow' i)
        (Finset.sum_nonneg fun x _ => hC i x) hchi
      _ = chi ^ 2 := by ring
  have hA4 : A4 ≤ chi ^ 2 := by
    dsimp [A4]
    calc
      _ = ∑ j : V, C j i * (∑ l : V, C j l) := by
        simp [Finset.mul_sum]
      _ ≤ ∑ j : V, C j i * chi := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hrow' j) (hC j i)
      _ = (∑ j : V, C j i) * chi := by rw [Finset.sum_mul]
      _ ≤ chi * chi := mul_le_mul_of_nonneg_right (hrow i) hchi
      _ = chi ^ 2 := by ring
  have hA5 : A5 ≤ chi ^ 2 := by
    dsimp [A5]
    calc
      _ = ∑ j : V, C j i * (∑ k : V, C j k) := by
        simp [Finset.mul_sum]
      _ ≤ ∑ j : V, C j i * chi := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hrow' j) (hC j i)
      _ = (∑ j : V, C j i) * chi := by rw [Finset.sum_mul]
      _ ≤ chi * chi := mul_le_mul_of_nonneg_right (hrow i) hchi
      _ = chi ^ 2 := by ring
  have hA6 : A6 ≤ chi ^ 2 := by
    dsimp [A6]
    calc
      _ = ∑ k : V, C k i * (∑ j : V, C k j) := by
        rw [Finset.sum_comm]
        simp [Finset.mul_sum]
      _ ≤ ∑ k : V, C k i * chi := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (hrow' k) (hC k i)
      _ = (∑ k : V, C k i) * chi := by rw [Finset.sum_mul]
      _ ≤ chi * chi := mul_le_mul_of_nonneg_right (hrow i) hchi
      _ = chi ^ 2 := by ring
  have hnonneg : 0 ≤ finiteCollisionIntegratedFourthCumulant G beta J i := by
    unfold finiteCollisionIntegratedFourthCumulant
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
      Finset.sum_nonneg fun l _ =>
        (finiteCollisionFourthWeight_nonneg_le G beta J hbeta hJ i j k l).1
  refine ⟨hnonneg, ?_⟩
  calc
    finiteCollisionIntegratedFourthCumulant G beta J i ≤
        ∑ j : V, ∑ k : V, ∑ l : V,
          finiteCollisionFourthMajorant G beta J i j k l := by
      unfold finiteCollisionIntegratedFourthCumulant
      exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
        Finset.sum_le_sum fun l _ =>
          (finiteCollisionFourthWeight_nonneg_le G beta J hbeta hJ i j k l).2
    _ = 2 * (A1 + A2 + A3 + A4 + A5 + A6) := by
      dsimp [A1, A2, A3, A4, A5, A6, C]
      simp only [finiteCollisionFourthMajorant]
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 12 * chi ^ 2 := by
      have hsum : A1 + A2 + A3 + A4 + A5 + A6 ≤ 6 * chi ^ 2 := by
        linarith
      nlinarith

theorem finiteParityFourthUrsell_eq_finiteIsing_of_distinct
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    finiteParityFourthUrsell G beta J i j k l =
      finiteIsingFourthUrsell G beta J i j k l := by
  have hpair (x y : V) (hxy : x ≠ y) :
      grahamPairSupport x y = {x, y} := by
    ext z
    simp only [grahamPairSupport, Finset.mem_symmDiff,
      Finset.mem_singleton, Finset.mem_insert]
    aesop
  have hquad : grahamFourSupport i j k l = {i, j, k, l} := by
    rw [grahamFourSupport, hpair i j hij, hpair k l hkl]
    ext z
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    aesop
  unfold finiteParityFourthUrsell finiteIsingFourthUrsell
  rw [hquad, hpair i j hij, hpair i k hik, hpair i l hil,
    hpair j k hjk, hpair j l hjl, hpair k l hkl]


end
end StatMech.FrontierA
