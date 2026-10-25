/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/IsingBoxEncoding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.IsingFK.FvES.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.EsWired.Part11
import Theorem.StatisticalMechanics.Code.IsingFK.EsInfinite.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2
import Theorem.StatisticalMechanics.Code.FK.EsCorrelations.Part4
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Def.StatisticalMechanics.Code.Ising.Magnetization.Part3
import Def.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part2
open MeasureTheory
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice StatMech.Ising StatMech.Percolation


section AbstractGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

variable (bdry : V → Prop) [DecidablePred bdry]


omit [DecidableEq V] in


theorem pottsWeightWired_eq_isingWiredWeight (β : ℝ) (σ : V → Fin 2) :
    pottsWeightWired G bdry (0 : Fin 2) (2 * β) 1 σ
      = Real.exp (β * G.edgeFinset.card) * isingWiredWeight G bdry β σ := by
  unfold pottsWeightWired isingWiredWeight Potts.pottsWeight
  by_cases h : BoundaryFixed bdry (0 : Fin 2) σ
  · rw [if_pos h, if_pos h, agreement_eq_isingBondSum, ← Real.exp_add]
    congr 1; ring
  · rw [if_neg h, if_neg h, mul_zero]


theorem esWiredOnePoint_eq_pottsWiredOnePoint (β J : ℝ) (x : V) :
    esWiredOnePoint G bdry (0 : Fin 2) (1 - Real.exp (-(β * J))) x
      = (∑ σ : V → Fin 2, pottsWeightWired G bdry (0 : Fin 2) β J σ * isingSpin (σ x))
          / pottsZWired G bdry 2 (0 : Fin 2) β J := by
  unfold esWiredOnePoint
  rw [esZWired_eq_pottsZWired]
  have hnum : (∑ ω : ConfigSpace (Sym2 V), ∑ σ : V → Fin 2,
        esWeightWired G bdry (0 : Fin 2) (1 - Real.exp (-(β * J))) σ ω * isingSpin (σ x))
      = esFirstConst G β J
          * ∑ σ : V → Fin 2, pottsWeightWired G bdry (0 : Fin 2) β J σ * isingSpin (σ x) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [← Finset.sum_mul, esWeightWired_sum_omega]; ring
  rw [hnum, mul_div_mul_left _ _ (esFirstConst_pos G β J).ne']


theorem esWiredOnePoint_eq_isingWiredOnePoint (β : ℝ) (x : V) :
    esWiredOnePoint G bdry (0 : Fin 2) (1 - Real.exp (-2 * β)) x
      = isingWiredOnePoint G bdry β x := by
  have hp : (1 - Real.exp (-2 * β)) = 1 - Real.exp (-((2 * β) * 1)) := by ring_nf
  rw [hp, esWiredOnePoint_eq_pottsWiredOnePoint]
  have hnum : (∑ σ : V → Fin 2, pottsWeightWired G bdry (0 : Fin 2) (2 * β) 1 σ * isingSpin (σ x))
      = Real.exp (β * G.edgeFinset.card)
          * ∑ σ : V → Fin 2, isingWiredWeight G bdry β σ * isingSpin (σ x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [pottsWeightWired_eq_isingWiredWeight]; ring
  have hden : pottsZWired G bdry 2 (0 : Fin 2) (2 * β) 1
      = Real.exp (β * G.edgeFinset.card) * isingWiredZ G bdry β := by
    unfold pottsZWired isingWiredZ
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun σ _ => pottsWeightWired_eq_isingWiredWeight G bdry β σ)
  rw [hnum, hden, isingWiredOnePoint, mul_div_mul_left _ _ (Real.exp_pos _).ne']


theorem esWiredOnePoint_pOfBeta_eq_isingWiredOnePoint (β : ℝ) (x : V) :
    esWiredOnePoint G bdry (0 : Fin 2) (pOfBeta β) x = isingWiredOnePoint G bdry β x := by
  rw [pOfBeta]; exact esWiredOnePoint_eq_isingWiredOnePoint G bdry β x

end AbstractGraph


section Lattice

variable {d : ℕ}


theorem fvMagnetization_eq_fvProb_sum (d : ℕ) (β : ℝ) (n : ℕ) :
    fvMagnetization d β n
      = ∑ τ : {x // x ∈ box d n} → Bool,
          fvProb (plusField d) n (bondFinsetTouch d n) β 0 τ
            * spin (glue (plusField d) τ) (origin d) := by
  unfold fvMagnetization plusMeasure fvProbabilityMeasure
  simp only [ProbabilityMeasure.coe_mk]
  rw [fvMeasure, integral_finsetSum_measure ?_]
  · refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [integral_smul_measure, MeasureTheory.integral_dirac, smul_eq_mul,
      ENNReal.toReal_ofReal (fvProb_nonneg _ _ _ _ _ _)]
  · intro τ _
    apply Integrable.smul_measure (integrable_spin _ _)
    simp [ENNReal.ofReal_ne_top]


end Lattice
end IsingFK
end StatMech
