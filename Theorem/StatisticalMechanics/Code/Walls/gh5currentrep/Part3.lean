/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh5currentrep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gh4eq22.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc85bthreereplicaswitch.Part3
import Def.StatisticalMechanics.Code.Walls.gh5currentrep.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent

open StatMech.Walls.GhcEqGap

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {W : Type*} [DecidableEq W] [Fintype W]


theorem gh5_complMass_eq_decoupled (ends : ι → Sym2 W) (m : Finset ι) (V₁ V₂ : Finset W) (u : W)
    (A : Finset ι) :
    gh5_complMass ends m V₁ V₂ u A = gh5_complMassDecoupled ends m V₁ V₂ u A := by
  classical
  unfold gh5_complMass gh5_complMassDecoupled
  congr 1
  apply Finset.filter_congr
  rintro ⟨K₁', K₂'⟩ hmem
  simp only [Finset.mem_product, Finset.mem_powerset] at hmem
  
  have hK₁A : Disjoint A K₁' := by
    rw [Finset.disjoint_left]
    intro a haA haK
    exact (Finset.mem_sdiff.1 (hmem.1 haK)).2 haA
  have hsplit : sources ends (A ∪ K₁') = sources ends A ∆ sources ends K₁' :=
    gh5_sources_union_of_disjoint ends hK₁A
  
  constructor
  · rintro ⟨hd, h1, h2, h3⟩
    refine ⟨hd, ?_, h2, h3⟩
    rw [hsplit] at h1
    
    rw [← h1, symmDiff_comm, symmDiff_symmDiff_cancel_left]
  · rintro ⟨hd, h1, h2, h3⟩
    refine ⟨hd, ?_, h2, h3⟩
    rw [hsplit, h1]
    rw [symmDiff_comm (sources ends A), symmDiff_assoc, symmDiff_self, symmDiff_bot]


theorem gh5_fact2_factorization (ends : ι → Sym2 W) (m : Finset ι) (V₁ V₂ : Finset W) (u : W)
    (A : Finset ι) (hAm : A ⊆ m) :
    gh4_compMass ends m V₁ V₂ u A = gh5_complMassDecoupled ends m V₁ V₂ u A := by
  rw [gh5_compMass_eq_complMass ends m V₁ V₂ u A hAm, gh5_complMass_eq_decoupled]


theorem gh5_fact1_ghost_collapse {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (o x y : V) :
    gh3_eq22_decomposition G β h o x y
      = (∃ surv dropA dropB : ℝ,
          eg_ursell3 G β h o x y = surv - 2 * dropA - 2 * dropB ∧ 0 ≤ dropA ∧ 0 ≤ dropB) := rfl


theorem gh5_drop_sum_factored (ends : ι → Sym2 W) (m : Finset ι) (V₁ V₂ : Finset W) (u : W)
    (wgt diff : Finset ι → ℝ) :
    (∑ A ∈ m.powerset, (gh4_compMass ends m V₁ V₂ u A : ℝ) * wgt A * diff A)
      = ∑ A ∈ m.powerset, (gh5_complMassDecoupled ends m V₁ V₂ u A : ℝ) * wgt A * diff A := by
  refine Finset.sum_congr rfl (fun A hA => ?_)
  rw [gh5_fact2_factorization ends m V₁ V₂ u A (Finset.mem_powerset.1 hA)]


theorem gh5_eq22_from_factored_identity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (o x y : V)
    (ends : ι → Sym2 W) (m : Finset ι) (V₁ V₂ V₁' V₂' : Finset W) (u u' : W)
    (wgtA diffA wgtB diffB : Finset ι → ℝ)
    (hwgtA : ∀ A, 0 ≤ wgtA A) (hdiffA : ∀ A, 0 ≤ diffA A)
    (hwgtB : ∀ B, 0 ≤ wgtB B) (hdiffB : ∀ B, 0 ≤ diffB B)
    (surv : ℝ)
    (hident : eg_ursell3 G β h o x y
      = surv
        - 2 * (∑ A ∈ m.powerset, (gh5_complMassDecoupled ends m V₁ V₂ u A : ℝ) * wgtA A * diffA A)
        - 2 * (∑ B ∈ m.powerset, (gh5_complMassDecoupled ends m V₁' V₂' u' B : ℝ) * wgtB B * diffB B)) :
    gh3_eq22_decomposition G β h o x y := by
  apply gh4_eq22_decomposition_of_identity G β h o x y ends m V₁ V₂ V₁' V₂' u u'
    wgtA diffA wgtB diffB hwgtA hdiffA hwgtB hdiffB surv
  rw [hident, gh5_drop_sum_factored ends m V₁ V₂ u wgtA diffA,
    gh5_drop_sum_factored ends m V₁' V₂' u' wgtB diffB]


theorem gh5_status : True := trivial

end StatMech.Walls
