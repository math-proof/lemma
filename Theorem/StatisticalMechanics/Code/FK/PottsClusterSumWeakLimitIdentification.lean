/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumContinuity.Part2
import Theorem.StatisticalMechanics.Code.FK.PottsInfiniteVolume.Part8
import Theorem.StatisticalMechanics.Code.FrontierB.FreeInfiniteMultipointES
import Def.StatisticalMechanics.Code.FK.PottsClusterSumWeakLimitIdentification
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem uniformClusterColor_map_apply
    (q : Nat) [NeZero q] (omega : ConfigSpace (Sym2 V))
    (sigma : V -> Fin q) :
    ((PMF.uniformOfFintype
      ((openSub G omega).ConnectedComponent -> Fin q)).map
        (IsingFK.coloring G omega)) sigma =
      if ConstOnOpen G omega sigma then
        ((q : ENNReal) ^ numClusters G omega)⁻¹
      else 0 := by
  classical
  by_cases hconst : ConstOnOpen G omega sigma
  · rw [if_pos hconst, PMF.map_apply]
    let tau : (openSub G omega).ConnectedComponent -> Fin q :=
      (constOnOpenEquiv G omega).symm ⟨sigma, hconst⟩
    rw [tsum_eq_single tau]
    · have htau : IsingFK.coloring G omega tau = sigma := by
        change ((constOnOpenEquiv G omega) tau).1 = sigma
        simpa [tau] using congrArg Subtype.val
          ((constOnOpenEquiv G omega).apply_symm_apply ⟨sigma, hconst⟩)
      rw [if_pos htau.symm]
      simp [Fintype.card_fun, Fintype.card_fin, numClusters]
    · intro tau' hne
      rw [if_neg]
      intro heq
      apply hne
      apply (constOnOpenEquiv G omega).injective
      apply Subtype.ext
      have htau : IsingFK.coloring G omega tau = sigma := by
        change ((constOnOpenEquiv G omega) tau).1 = sigma
        simpa [tau] using congrArg Subtype.val
          ((constOnOpenEquiv G omega).apply_symm_apply ⟨sigma, hconst⟩)
      exact heq.symm.trans htau.symm
  · rw [if_neg hconst, PMF.map_apply]
    rw [tsum_fintype]
    apply Finset.sum_eq_zero
    intro tau _
    rw [if_neg]
    intro heq
    apply hconst
    rw [heq]
    exact (IsingFK.compatible_iff_constOnOpen G _ _).mp
      (IsingFK.coloring_compatible G omega tau)


theorem freeClusterColorJointPMF_eq_ivp_freeJointPMF
    (q : Nat) [NeZero q] {p : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < (q : Real)) :
    freeClusterColorJointPMF G q hp hp1 hq =
      ivp_freeJointPMF G q hp hp1 hq := by
  classical
  ext z
  rcases z with ⟨sigma, omega⟩
  rw [freeClusterColorJointPMF, PMF.bind_apply, tsum_fintype]
  rw [Finset.sum_eq_single omega]
  · simp only [PMF.map_apply]
    have hpair : (∑' tau : (openSub G omega).ConnectedComponent -> Fin q,
        if sigma = IsingFK.coloring G omega tau then
          PMF.uniformOfFintype
            ((openSub G omega).ConnectedComponent -> Fin q) tau
        else 0) =
        ((PMF.uniformOfFintype
          ((openSub G omega).ConnectedComponent -> Fin q)).map
            (IsingFK.coloring G omega)) sigma := by
      rw [PMF.map_apply]
      apply tsum_congr
      intro tau
      rw [eq_comm]
      by_cases h : sigma = IsingFK.coloring G omega tau
      · simp only [if_pos h]
      · simp only [if_neg h]
    simp only [Prod.mk.injEq, and_true]
    rw [hpair, uniformClusterColor_map_apply G q omega sigma]
    simp only [ivp_freeJointPMF, PMF.ofFintype_apply, fkPMF_apply]
    rw [ivp_freeJointProb_eq_fkProb_div_pow G hq]
    by_cases hconst : ConstOnOpen G omega sigma
    · simp only [if_pos hconst]
      rw [ENNReal.ofReal_div_of_pos]
      · simp [div_eq_mul_inv]
      · positivity
    · simp [hconst]
  · intro omega' _ hne
    simp [hne, Ne.symm hne]
  · simp


end StatMech.FK
