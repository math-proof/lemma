/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/FvES.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.EsCorrelations.Part4
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Theorem.StatisticalMechanics.Code.IsingFK.EsWired.Part11
import Theorem.StatisticalMechanics.Code.IsingFK.EsLatticeBridge
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.IsingFK.FvES.Part3
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

variable (bdry : V → Prop) [DecidablePred bdry]


theorem esWiredOnePoint_eq_wiredConnToBdryProb (p : ℝ) (x : V) (v₀ : V) (hv₀ : bdry v₀) :
    esWiredOnePoint G bdry (0 : Fin 2) p x = wiredConnToBdryProb G bdry p x := by
  classical
  unfold esWiredOnePoint wiredConnToBdryProb
  have hnum : (2 : ℝ) * (∑ ω : ConfigSpace (Sym2 V), ∑ σ : V → Fin 2,
        esWeightWired G bdry (0 : Fin 2) p σ ω * isingSpin (σ x))
      = ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ConnToBdry G bdry ω x),
          bcWeight G (boundaryCliqueGraph bdry) p (2 : ℝ) ω := by
    rw [Finset.mul_sum]
    have hterm : ∀ ω : ConfigSpace (Sym2 V),
        (2 : ℝ) * (∑ σ : V → Fin 2, esWeightWired G bdry (0 : Fin 2) p σ ω * isingSpin (σ x))
          = if ConnToBdry G bdry ω x then bcWeight G (boundaryCliqueGraph bdry) p (2:ℝ) ω
            else 0 := by
      intro ω
      rw [esWeightWired_spin_sum G bdry p ω v₀ hv₀ x]
      by_cases h : ConnToBdry G bdry ω x
      · rw [if_pos h, if_pos h, edgeProduct_pow_eq_bcWeight_half G bdry p ω v₀]
      · rw [if_neg h, if_neg h, mul_zero, mul_zero]
    rw [Finset.sum_congr rfl (fun ω _ => hterm ω)]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun ω : ConfigSpace (Sym2 V) => ConnToBdry G bdry ω x)]
    have h0 : (∑ ω ∈ Finset.univ.filter
          (fun ω : ConfigSpace (Sym2 V) => ¬ ConnToBdry G bdry ω x),
          (if ConnToBdry G bdry ω x then bcWeight G (boundaryCliqueGraph bdry) p (2:ℝ) ω
            else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro ω hω
      rw [if_neg (Finset.mem_filter.1 hω).2]
    rw [h0, add_zero]
    apply Finset.sum_congr rfl
    intro ω hω
    rw [if_pos (Finset.mem_filter.1 hω).2]
  have hden : (2 : ℝ) * esZWired G bdry 2 (0 : Fin 2) p
      = bcZ G (boundaryCliqueGraph bdry) p (2 : ℝ) :=
    esZWired_eq_bcZ G bdry (0 : Fin 2) p v₀ hv₀ (fun ω => one_le_numClustersBC G bdry v₀ ω)
  rw [show ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ConnToBdry G bdry ω x),
        bcProb G (boundaryCliqueGraph bdry) p (2 : ℝ) ω
      = (∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ConnToBdry G bdry ω x),
          bcWeight G (boundaryCliqueGraph bdry) p (2 : ℝ) ω)
          / bcZ G (boundaryCliqueGraph bdry) p (2 : ℝ) from by
        unfold bcProb; rw [Finset.sum_div]]
  rw [← hnum, ← hden, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]


theorem wiredConnToBdryProb_eq_wiredFkProb_sum (p : ℝ) (x : V) :
    wiredConnToBdryProb G bdry p x
      = ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ConnToBdry G bdry ω x),
          wiredFkProb G bdry p (2 : ℝ) ω := by
  unfold wiredConnToBdryProb
  exact Finset.sum_congr rfl (fun ω _ => (wiredFkProb_eq_bcProb G bdry p (2 : ℝ) ω).symm)

end IsingFK
end StatMech
