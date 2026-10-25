/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeMultipointEdwardsSokal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FK.EsCorrelations.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Def.StatisticalMechanics.Code.FrontierB.FreeMultipointEdwardsSokal.Part2
open scoped BigOperators


namespace StatMech.FK

open StatMech.ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]


theorem esSpinProduct_constOnOpenEquiv (omega : ConfigSpace (Sym2 V))
    (A : Finset V) (tau : (openSub G omega).ConnectedComponent -> Fin 2) :
    esSpinProduct A ((constOnOpenEquiv G omega tau).1) =
      ∏ C : (openSub G omega).ConnectedComponent,
        isingSpin (tau C) ^ clusterMarkCount G omega A C := by
  classical
  unfold esSpinProduct clusterMarkCount
  change (∏ x ∈ A,
      isingSpin (tau ((openSub G omega).connectedComponentMk x))) = _
  rw [← Finset.prod_fiberwise' A
    (fun x => (openSub G omega).connectedComponentMk x)
    (fun C => isingSpin (tau C))]
  apply Fintype.prod_congr
  intro C
  rw [Finset.prod_const]

theorem sum_isingSpin_pow (n : Nat) :
    (∑ a : Fin 2, isingSpin a ^ n) = if Even n then 2 else 0 := by
  by_cases h : Even n
  · rw [Fin.sum_univ_two]
    simp [isingSpin, h, h.neg_one_pow]
    norm_num
  · rw [Fin.sum_univ_two]
    simp [isingSpin, h, neg_one_pow_eq_ite]


theorem clusterColor_spinProduct_sum (omega : ConfigSpace (Sym2 V))
    (A : Finset V) :
    (∑ tau : (openSub G omega).ConnectedComponent -> Fin 2,
        esSpinProduct A ((constOnOpenEquiv G omega tau).1)) =
      if AllClustersEven G omega A then 2 ^ numClusters G omega else 0 := by
  classical
  simp_rw [esSpinProduct_constOnOpenEquiv G omega A]
  calc
    (∑ tau : (openSub G omega).ConnectedComponent -> Fin 2,
        ∏ C, isingSpin (tau C) ^ clusterMarkCount G omega A C) =
        ∏ C : (openSub G omega).ConnectedComponent,
          ∑ a : Fin 2, isingSpin a ^ clusterMarkCount G omega A C := by
            simpa [Fintype.piFinset_univ] using
              (Finset.sum_prod_piFinset (Finset.univ : Finset (Fin 2))
                (fun C a => isingSpin a ^ clusterMarkCount G omega A C))
    _ = ∏ C : (openSub G omega).ConnectedComponent,
          if Even (clusterMarkCount G omega A C) then 2 else 0 := by
            apply Fintype.prod_congr
            intro C
            exact sum_isingSpin_pow (clusterMarkCount G omega A C)
    _ = if AllClustersEven G omega A then 2 ^ numClusters G omega else 0 := by
          by_cases hEven : AllClustersEven G omega A
          · rw [if_pos hEven]
            simp_rw [if_pos (hEven _)]
            simp [numClusters]
          · rw [if_neg hEven]
            have hnot : ¬ ∀ C : (openSub G omega).ConnectedComponent,
                Even (clusterMarkCount G omega A C) := by
              simpa [AllClustersEven] using hEven
            rw [Classical.not_forall] at hnot
            obtain ⟨C, hC⟩ := hnot
            apply Finset.prod_eq_zero (Finset.mem_univ C)
            rw [if_neg hC]


theorem compatible_esSpinProduct_sum (omega : ConfigSpace (Sym2 V))
    (A : Finset V) :
    (∑ sigma : V -> Fin 2,
        (if ConstOnOpen G omega sigma then (1 : Real) else 0) *
          esSpinProduct A sigma) =
      if AllClustersEven G omega A then 2 ^ numClusters G omega else 0 := by
  classical
  calc
    (∑ sigma : V -> Fin 2,
        (if ConstOnOpen G omega sigma then (1 : Real) else 0) *
          esSpinProduct A sigma) =
        ∑ sigma ∈ Finset.univ.filter (ConstOnOpen G omega),
          esSpinProduct A sigma := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro sigma hsigma
            by_cases h : ConstOnOpen G omega sigma
            · simp [h]
            · simp [h]
    _ = ∑ sigma : {sigma : V -> Fin 2 // ConstOnOpen G omega sigma},
          esSpinProduct A sigma.1 := by
            rw [Finset.sum_subtype]
            intro sigma
            simp
    _ = ∑ tau : (openSub G omega).ConnectedComponent -> Fin 2,
          esSpinProduct A ((constOnOpenEquiv G omega tau).1) := by
            symm
            exact (constOnOpenEquiv G omega).sum_comp
              (fun sigma => esSpinProduct A sigma.1)
    _ = if AllClustersEven G omega A then 2 ^ numClusters G omega else 0 :=
      clusterColor_spinProduct_sum G omega A


theorem esWeight_multipoint_spin_sum (p : Real)
    (omega : ConfigSpace (Sym2 V)) (A : Finset V) :
    (∑ sigma : V -> Fin 2,
        esWeight G p sigma omega * esSpinProduct A sigma) =
      if AllClustersEven G omega A then fkWeight G p (2 : Real) omega else 0 := by
  rw [esWeight_spinsum_factor,
    compatible_esSpinProduct_sum G omega A]
  by_cases hEven : AllClustersEven G omega A
  · rw [if_pos hEven, if_pos hEven]
    rfl
  · rw [if_neg hEven, if_neg hEven, mul_zero]


end StatMech.FK
