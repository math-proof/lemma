/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxDomainMarkov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part2
open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

variable (C : SimpleGraph V) [DecidableRel C.Adj]


theorem bcProb_fibre_decompose {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (B : Set (ConfigSpace (Sym2 V))) :
    (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * bcProb G C p q ρ)
      = ∑ ψ ∈ fibreReps F,
          (∑ σ ∈ condFibre F ψ, bcProb G C p q σ)
          * (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := projOff F) (t := fibreReps F)
      (fun ρ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, projOff_idem F ρ⟩)]
  apply Finset.sum_congr rfl
  intro ψ hψ
  rw [fibreReps, Finset.mem_filter] at hψ
  rw [show (Finset.univ.filter (fun ρ => projOff F ρ = ψ)) = condFibre F ψ from
        filter_projOff_eq_condFibre F ψ hψ.2]
  have hRHS : (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ)
      = ∑ ρ ∈ condFibre F ψ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro ρ _ hρ
    rw [mem_condFibre] at hρ
    unfold condBcProb
    rw [if_neg hρ, mul_zero]
  rw [hRHS, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [mem_condFibre] at hρ
  have hbc := bcProb_eq_fibreMass_mul_condBcProb G C hp hp1 hq F ρ
  have hfib : condFibre F ρ = condFibre F ψ := by
    ext σ; rw [mem_condFibre, mem_condFibre, agreesOff_congr (agreesOff_symm hρ)]
  rw [hfib] at hbc
  have hcc : condBcProb G C p q F ρ ρ = condBcProb G C p q F ψ ρ :=
    condBcProb_congr_dom' G C p q F ρ ψ ρ (agreesOff_symm hρ)
  rw [hcc] at hbc
  rw [hbc]; ring


end FK
end StatMech
