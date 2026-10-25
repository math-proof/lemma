/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc31surgery.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc30reroute
import Theorem.StatisticalMechanics.Code.Ising.BackboneResummation.Part2
import Theorem.StatisticalMechanics.Code.Ising.BackboneExists
import Theorem.StatisticalMechanics.Code.Ising.HdomMultiplicity.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc7ghosteven
import Def.StatisticalMechanics.Code.Walls.gc31surgery
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc31_backboneSurgery_of_massDoubling (β : ℝ) (J : Sym2 V → ℝ)
    (M : Finset (Sharpness.Current V)) (B : Finset V) (o x y : V)
    (h : gc31_MassDoublingSurgery G β J M B o x y) :
    bbr_BackboneSurgery G β J M B o x y := by
  obtain ⟨Φ, hmem, hinj, hbound⟩ := h
  exact ⟨Φ, hmem, fun a ha a' ha' => hinj ha ha', hbound⟩


theorem gc31_native_gap_nonneg_of_massDoubling (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β)
    (hJ : ∀ e, 0 ≤ J e) (M : Finset (Sharpness.Current V))
    (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (B : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = B) {o x y : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (hcoh : ∀ m ∈ M, hnw_coherent G m o x y)
    (h : gc31_MassDoublingSurgery G β J M B o x y) :
    0 ≤ ∑ m ∈ M, hnw_gap G β J m B o x y :=
  gc30_native_gap_nonneg_of_backboneSurgery G β J hβ hJ M hnd B hm hox hoy hxy hcoh
    (gc31_backboneSurgery_of_massDoubling G β J M B o x y h)


theorem gc31_massDoubling_of_singleton_dominated (β : ℝ) (J : Sym2 V → ℝ)
    (M : Finset (Sharpness.Current V)) (B : Finset V) (o x y : V)
    (ma mstar : Sharpness.Current V)
    (hsingle : bbr_allFilter G M o x y = {ma})
    (hstar : mstar ∈ bbr_noneFilter G M o x y)
    (hdom : 2 * hnw_mass G β J ma B ≤ hnw_mass G β J mstar B) :
    gc31_MassDoublingSurgery G β J M B o x y := by
  refine ⟨fun _ => mstar, ?_, ?_, ?_⟩
  · intro m hm; exact hstar
  · intro a ha a' ha' _
    rw [hsingle, Finset.coe_singleton, Set.mem_singleton_iff] at ha ha'
    rw [ha, ha']
  · intro m hm
    rw [hsingle, Finset.mem_singleton] at hm
    rw [hm]; exact hdom


theorem gc31_mass_zero_of_odd_card (β : ℝ) (J : Sym2 V → ℝ) (m : Sharpness.Current V)
    (S : Finset V) (hodd : ¬ Even S.card) :
    hnw_mass G β J m S = 0 := by
  unfold hnw_mass splitWeightedSum
  apply Finset.sum_eq_zero
  intro K _
  rw [if_neg]
  intro hK
  exact hodd (hK ▸ gc7_sources_card_even G K.1)


theorem gc31_connP_empty_eq {a b : V} (h : connP (∅ : Finset (Sym2 V)) a b) : a = b := by
  induction h with
  | refl => rfl
  | tail _ hstep _ => obtain ⟨e, he, _, _, _⟩ := hstep; exact absurd he (Finset.notMem_empty e)


end StatMech.Walls
