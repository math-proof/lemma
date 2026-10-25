/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/HisingBoxClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
import Theorem.StatisticalMechanics.Code.Lattice.ClusterContourBijection.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.MagnetizationCorrespondence
import Def.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part2
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.Ising StatMech.FK StatMech.Lattice StatMech.Percolation

variable {d n : ℕ}


theorem hbx_sum_reindex (d n : ℕ) (f : (boxVerts d (n + 1) → Fin 2) → ℝ)
    (hf : ∀ σ, ¬ BoundaryFixed (boxBoundary d (n + 1)) (0 : Fin 2) σ → f σ = 0) :
    ∑ σ : boxVerts d (n + 1) → Fin 2, f σ
      = ∑ τ : {x // x ∈ box d n} → Bool, f (latToBox d n τ) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun σ => BoundaryFixed (boxBoundary d (n + 1)) (0 : Fin 2) σ)]
  have hz : ∑ σ ∈ Finset.univ.filter
        (fun σ => ¬ BoundaryFixed (boxBoundary d (n + 1)) (0 : Fin 2) σ), f σ = 0 := by
    apply Finset.sum_eq_zero; intro σ hσ; exact hf σ (Finset.mem_filter.1 hσ).2
  rw [hz, add_zero,
    Finset.sum_subtype (p := fun σ => BoundaryFixed (boxBoundary d (n + 1)) (0 : Fin 2) σ)
      (Finset.univ.filter (fun σ => BoundaryFixed (boxBoundary d (n + 1)) (0 : Fin 2) σ))
      (fun σ => by simp) f,
    ← (hbx_latBoxEquiv d n).sum_comp
      (fun σ : {σ // BoundaryFixed (boxBoundary d (n + 1)) (0 : Fin 2) σ} => f σ.1)]
  rfl


theorem hbx_fvWeight_eq (d n : ℕ) (β : ℝ) (τ : {x // x ∈ box d n} → Bool) :
    fvWeight (plusField d) n (bondFinsetTouch d n) β 0 τ
      = Real.exp (β * ∑ e ∈ bondFinsetTouch d n, bond (glue (plusField d) τ) e) := by
  unfold fvWeight fvEnergy
  congr 1; ring


theorem hbx_isingWiredWeight_latToBox (d n : ℕ) (β : ℝ) (τ : {x // x ∈ box d n} → Bool) :
    isingWiredWeight (boxGraph d (n + 1)) (boxBoundary d (n + 1)) β (latToBox d n τ)
      = Real.exp (β * ((Finset.image (edgeIncl d (n + 1)) (boxGraph d (n + 1)).edgeFinset)
              \ bondFinsetTouch d n).card)
          * fvWeight (plusField d) n (bondFinsetTouch d n) β 0 τ := by
  unfold isingWiredWeight
  rw [if_pos (boundaryFixed_latToBox d n τ), hbx_edge_energy, hbx_fvWeight_eq,
    mul_add, Real.exp_add]
  ring


theorem hbx_isingWiredOnePoint_eq_fvMagnetization (d n : ℕ) (β : ℝ) :
    isingWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) β (boxOrigin d (n + 1))
      = fvMagnetization d β n := by
  classical
  set C : ℝ := (((Finset.image (edgeIncl d (n + 1)) (boxGraph d (n + 1)).edgeFinset)
      \ bondFinsetTouch d n).card : ℝ) with hCdef
  set E : ℝ := Real.exp (β * C) with hEdef
  have hE0 : E ≠ 0 := (Real.exp_pos _).ne'
  
  have hnum : (∑ σ : boxVerts d (n + 1) → Fin 2,
        isingWiredWeight (boxGraph d (n + 1)) (boxBoundary d (n + 1)) β σ
          * isingSpin (σ (boxOrigin d (n + 1))))
      = E * ∑ τ : {x // x ∈ box d n} → Bool,
          fvWeight (plusField d) n (bondFinsetTouch d n) β 0 τ
            * spin (glue (plusField d) τ) (Ising.origin d) := by
    rw [hbx_sum_reindex d n
      (fun σ => isingWiredWeight (boxGraph d (n + 1)) (boxBoundary d (n + 1)) β σ
        * isingSpin (σ (boxOrigin d (n + 1))))
      (fun σ hσ => by simp only [isingWiredWeight, if_neg hσ, zero_mul])]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [hbx_isingWiredWeight_latToBox]
    have hspin : isingSpin (latToBox d n τ (boxOrigin d (n + 1)))
        = spin (glue (plusField d) τ) (Ising.origin d) := by
      rw [isingSpin_latToBox]; rfl
    rw [hspin, ← hEdef]; ring
  
  have hden : isingWiredZ (boxGraph d (n + 1)) (boxBoundary d (n + 1)) β
      = E * fvZ (plusField d) n (bondFinsetTouch d n) β 0 := by
    unfold isingWiredZ fvZ
    rw [hbx_sum_reindex d n
      (fun σ => isingWiredWeight (boxGraph d (n + 1)) (boxBoundary d (n + 1)) β σ)
      (fun σ hσ => by simp only [isingWiredWeight, if_neg hσ]),
      Finset.mul_sum]
    exact Finset.sum_congr rfl (fun τ _ => hbx_isingWiredWeight_latToBox d n β τ)
  
  rw [isingWiredOnePoint, hnum, hden, mul_div_mul_left _ _ hE0,
    fvMagnetization_eq_fvProb_sum]
  unfold fvProb
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [show Ising.origin d = Percolation.origin d from rfl]
  ring


theorem hbx_hisingBox (d : ℕ) :
    ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n
        = esWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) (0 : Fin 2)
            (pOfBeta β) (boxOrigin d (n + 1)) := by
  intro β _ n _
  rw [esWiredOnePoint_pOfBeta_eq_isingWiredOnePoint,
    hbx_isingWiredOnePoint_eq_fvMagnetization]


theorem hbx_htransition (d : ℕ) (hd : 1 ≤ d)
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc1 : FK.fkPc d 2 < 1) :
    ∀ β, 0 < β → (0 < magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β) :=
  Ising.mfc_htransition d hd (hbx_hisingBox d) hFKsub hpc1


theorem hbx_ising_transition (d : ℕ) (hd : 1 ≤ d)
    (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc0 : 0 < FK.fkPc d 2) (hpc1 : FK.fkPc d 2 < 1) :
    ∃ βc : ℝ, 0 < βc ∧
      (∀ β, 0 < β → β < βc → magnetization d β = 0) ∧
      (∀ β, βc < β → 0 < magnetization d β) :=
  Ising.mfc_ising_transition d hd hmag_nonneg (hbx_hisingBox d) hFKsub hpc0 hpc1


theorem hbx_isingBetaC_eq (d : ℕ) (hd : 1 ≤ d)
    (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc0 : 0 < FK.fkPc d 2) (hpc1 : FK.fkPc d 2 < 1) :
    IsingFK.betaC (magnetization d) = -(1 / 2) * Real.log (1 - FK.fkPc d 2) :=
  Ising.mfc_isingBetaC_eq d hd hmag_nonneg (hbx_hisingBox d) hFKsub hpc0 hpc1


theorem hbx_isingBetaC_pos (d : ℕ) (hd : 1 ≤ d)
    (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc0 : 0 < FK.fkPc d 2) (hpc1 : FK.fkPc d 2 < 1) :
    0 < IsingFK.betaC (magnetization d) :=
  Ising.mfc_isingBetaC_pos d hd hmag_nonneg (hbx_hisingBox d) hFKsub hpc0 hpc1

end IsingFK
end StatMech
