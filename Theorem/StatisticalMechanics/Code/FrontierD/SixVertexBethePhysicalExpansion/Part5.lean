/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part5
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexBetheConstrainedLocal_eq_IE
    {n : Nat} (N : Nat) (c : Real) (z : Fin (n + 1) -> Complex)
    (x : Fin (n + 1) -> Int) (S : Finset (Fin (n + 1)))
    (hS : SixVertexBetheNoAdjacent S) (i : Fin (n + 1)) :
    (if i ∈ S then z i ^ x i
      else if (finRotate (n + 1)).symm i ∈ S then
        z i ^ (sixVertexBetheShiftCoordinates N x i)
      else sixVertexBetheL c (z i) *
          z i ^ (sixVertexBetheShiftCoordinates N x i) +
        sixVertexBetheM c (z i) * z i ^ x i) =
      sixVertexBetheIELowerCoefficient c z S i *
          z i ^ (sixVertexBetheShiftCoordinates N x i) +
        sixVertexBetheIEUpperCoefficient c z S i * z i ^ x i := by
  by_cases hi : i ∈ S
  · have hpred : (finRotate (n + 1)).symm i ∉ S := by
      intro hpred
      apply hS ((finRotate (n + 1)).symm i) hpred
      simpa using hi
    have hpred' : i - 1 ∉ S := by simpa using hpred
    simp [sixVertexBetheIELowerCoefficient,
      sixVertexBetheIEUpperCoefficient, hi, hpred']
  · by_cases hpred : (finRotate (n + 1)).symm i ∈ S
    · have hpred' : i - 1 ∈ S := by simpa using hpred
      simp [sixVertexBetheIELowerCoefficient,
        sixVertexBetheIEUpperCoefficient, hi, hpred']
    · have hpred' : i - 1 ∉ S := by simpa using hpred
      simp [sixVertexBetheIELowerCoefficient,
        sixVertexBetheIEUpperCoefficient, hi, hpred']


theorem sixVertexBetheCollisionFreeIntervalSum_eq_rawWords
    {n : Nat} (N : Nat) (c : Real) (z : Fin (n + 1) -> Complex)
    (x : Fin (n + 1) -> Int)
    (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i < x i)
    (hz0 : ∀ i, z i ≠ 0) (hz1 : ∀ i, z i ≠ 1) :
    sixVertexBetheCollisionFreeIntervalSum N c z x =
      ∑ w ∈ (Finset.univ : Finset (Fin (n + 1))).powerset,
        sixVertexBetheRawIEWordCoefficient c z w *
          ((∏ i ∈ w,
              z i ^ (sixVertexBetheShiftCoordinates N x i)) *
            ∏ i ∈ (Finset.univ \ w), z i ^ x i) := by
  classical
  rw [sixVertexBetheCollisionFreeIntervalSum_inclusionExclusion]
  let P := (Finset.univ : Finset (Fin (n + 1))).powerset
  let Q := P.filter SixVertexBetheNoAdjacent
  calc
    (∑ S ∈ P, (-1 : Complex) ^ S.card *
        sixVertexBetheCollisionConstrainedIntervalSum N c z x S) =
      ∑ S ∈ Q, (-1 : Complex) ^ S.card *
        sixVertexBetheCollisionConstrainedIntervalSum N c z x S := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro S hSP hSQ
        have hnmem : S ∉ Q := hSQ
        have hnS : ¬ SixVertexBetheNoAdjacent S := by
          simpa [Q, hSP] using hnmem
        rw [sixVertexBetheCollisionConstrainedIntervalSum_eq_zero
          N c z x S hgap hnS, mul_zero]
    _ = ∑ S ∈ Q, (-1 : Complex) ^ S.card *
        ∏ i, (sixVertexBetheIELowerCoefficient c z S i *
              z i ^ (sixVertexBetheShiftCoordinates N x i) +
            sixVertexBetheIEUpperCoefficient c z S i * z i ^ x i) := by
      apply Finset.sum_congr rfl
      intro S hS
      have hno : SixVertexBetheNoAdjacent S := by
        exact (Finset.mem_filter.mp hS).2
      rw [sixVertexBetheCollisionConstrainedIntervalSum_eq_LMprod
        N c z x S hno hgap hz0 hz1]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      exact sixVertexBetheConstrainedLocal_eq_IE N c z x S hno i
    _ = ∑ w ∈ P,
        sixVertexBetheRawIEWordCoefficient c z w *
          ((∏ i ∈ w,
              z i ^ (sixVertexBetheShiftCoordinates N x i)) *
            ∏ i ∈ (Finset.univ \ w), z i ^ x i) := by
      simp_rw [Finset.prod_add, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w hw
      unfold sixVertexBetheRawIEWordCoefficient
      change (∑ S ∈ Q,
          (-1 : Complex) ^ S.card *
            ((∏ i ∈ w,
                sixVertexBetheIELowerCoefficient c z S i *
                  z i ^ (sixVertexBetheShiftCoordinates N x i)) *
              ∏ i ∈ (Finset.univ \ w),
                sixVertexBetheIEUpperCoefficient c z S i * z i ^ x i)) =
        (∑ S ∈ Q, (-1 : Complex) ^ S.card *
            ((∏ i ∈ w, sixVertexBetheIELowerCoefficient c z S i) *
              ∏ i ∈ (Finset.univ \ w),
                sixVertexBetheIEUpperCoefficient c z S i)) *
          ((∏ i ∈ w,
              z i ^ (sixVertexBetheShiftCoordinates N x i)) *
            ∏ i ∈ (Finset.univ \ w), z i ^ x i)
      calc
        (∑ S ∈ Q,
            (-1 : Complex) ^ S.card *
              ((∏ i ∈ w,
                  sixVertexBetheIELowerCoefficient c z S i *
                    z i ^ (sixVertexBetheShiftCoordinates N x i)) *
                ∏ i ∈ (Finset.univ \ w),
                  sixVertexBetheIEUpperCoefficient c z S i * z i ^ x i)) =
          ∑ S ∈ Q,
            (((-1 : Complex) ^ S.card *
              ((∏ i ∈ w, sixVertexBetheIELowerCoefficient c z S i) *
                ∏ i ∈ (Finset.univ \ w),
                  sixVertexBetheIEUpperCoefficient c z S i)) *
              ((∏ i ∈ w,
                  z i ^ (sixVertexBetheShiftCoordinates N x i)) *
                ∏ i ∈ (Finset.univ \ w), z i ^ x i)) := by
            apply Finset.sum_congr rfl
            intro S hS
            rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
            ring
        _ = _ := by rw [Finset.sum_mul]

theorem sum_powerset_neg_one_mul_complement_prod
    {α : Type} [Fintype α] [DecidableEq α]
    (T : Finset α) (b : α -> Complex) :
    (∑ S ∈ T.powerset, (-1 : Complex) ^ S.card *
      ∏ i, if i ∈ S then 1 else b i) =
    ∏ i, if i ∈ T then b i - 1 else b i := by
  have hcomp (S : Finset α) (hS : S ⊆ T) :
      (Finset.univ \ S) = (T \ S) ∪ (Finset.univ \ T) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union]
    tauto
  calc
    (∑ S ∈ T.powerset, (-1 : Complex) ^ S.card *
      ∏ i, if i ∈ S then 1 else b i) =
      ∑ S ∈ T.powerset,
        ((-1 : Complex) ^ S.card * ∏ i ∈ T \ S, b i) *
          ∏ i ∈ Finset.univ \ T, b i := by
      apply Finset.sum_congr rfl
      intro S hS
      have hST : S ⊆ T := Finset.mem_powerset.mp hS
      rw [Finset.prod_ite]
      simp only [Finset.prod_const_one, one_mul]
      have hfilter : (Finset.univ.filter fun i => i ∉ S) =
          Finset.univ \ S := by
        ext i
        simp
      rw [hfilter, hcomp S hST, Finset.prod_union]
      · ring
      · rw [Finset.disjoint_left]
        intro i hiT hiU
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hiT hiU
        exact hiU hiT.1
    _ = (∑ S ∈ T.powerset,
        (-1 : Complex) ^ S.card * ∏ i ∈ T \ S, b i) *
          ∏ i ∈ Finset.univ \ T, b i := by rw [Finset.sum_mul]
    _ = (∏ i ∈ T, (b i - 1)) *
          ∏ i ∈ Finset.univ \ T, b i := by
      rw [Finset.prod_sub]
      simp only [Finset.prod_const_one, mul_one]
    _ = ∏ i, if i ∈ T then b i - 1 else b i := by
      rw [Finset.prod_ite]
      congr 2 <;> ext i <;> simp


end
end StatMech.FrontierD
