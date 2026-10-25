/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIFromPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.IsingTranslatedBoxClose.Part3
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtreme
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Def.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part8
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

open StatMech.FK

open StatMech.Percolation

variable {d : ℕ}


theorem gvRes_gvOvr {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    (σ : {x // x ∈ Sout} → Bool) (τ : {x // x ∈ Sin} → Bool) :
    gvRes hsub (gvOvr hsub σ τ) = τ := by
  funext x; simp only [gvRes, gvOvr]; rw [dif_pos x.2]

theorem gvOvr_gvOvr_gvRes {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    (σ : {x // x ∈ Sout} → Bool) (τ : {x // x ∈ Sin} → Bool) :
    gvOvr hsub (gvOvr hsub σ τ) (gvRes hsub σ) = σ := by
  funext x; simp only [gvOvr, gvRes]
  by_cases hn : (x : Site d) ∈ Sin
  · rw [dif_pos hn]
  · rw [dif_neg hn, dif_neg hn]


theorem gvGlue_gvGlue_eq_gvGlue_ovr {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    (η : ConfigSpace (Site d)) (σ : {x // x ∈ Sout} → Bool) (τ : {x // x ∈ Sin} → Bool) :
    gvGlue (gvGlue η Sout σ) Sin τ = gvGlue η Sout (gvOvr hsub σ τ) := by
  funext x
  by_cases hn : x ∈ Sin
  · have hm : x ∈ Sout := hsub hn
    rw [gvGlue_mem _ _ _ hn, gvGlue_mem _ _ _ hm]; simp only [gvOvr, dif_pos hn]
  · by_cases hm : x ∈ Sout
    · rw [gvGlue_not_mem _ _ _ hn, gvGlue_mem _ _ _ hm, gvGlue_mem _ _ _ hm]
      simp only [gvOvr, dif_neg hn]
    · rw [gvGlue_not_mem _ _ _ hn, gvGlue_not_mem _ _ _ hm, gvGlue_not_mem _ _ _ hm]


theorem gvGlue_ovr_eq_off {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    (η : ConfigSpace (Site d)) (σ : {x // x ∈ Sout} → Bool) (τ : {x // x ∈ Sin} → Bool)
    {x : Site d} (hx : x ∉ Sin) :
    gvGlue η Sout (gvOvr hsub σ τ) x = gvGlue η Sout σ x := by
  by_cases hm : x ∈ Sout
  · rw [gvGlue_mem _ _ _ hm, gvGlue_mem _ _ _ hm]; simp only [gvOvr, dif_neg hx]
  · rw [gvGlue_not_mem _ _ _ hm, gvGlue_not_mem _ _ _ hm]


theorem gv_bond_glue_ovr_eq_of_notMem {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    (η : ConfigSpace (Site d)) (σ : {x // x ∈ Sout} → Bool) (τ : {x // x ∈ Sin} → Bool)
    {e : Sym2 (Site d)} (heE : e ∈ (hypercubicLattice d).edgeSet) (heB : e ∉ gvBondTouch Sin) :
    bond (gvGlue η Sout (gvOvr hsub σ τ)) e = bond (gvGlue η Sout σ) e := by
  induction e with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet] at heE
    rw [bond_mk, bond_mk]
    have ha : a ∉ Sin := fun h => heB (gv_mk_mem_bondTouch heE (Or.inl h))
    have hb : b ∉ Sin := fun h => heB (gv_mk_mem_bondTouch heE (Or.inr h))
    rw [show spin (gvGlue η Sout (gvOvr hsub σ τ)) a = spin (gvGlue η Sout σ) a from by
          unfold spin; rw [gvGlue_ovr_eq_off hsub η σ τ ha],
        show spin (gvGlue η Sout (gvOvr hsub σ τ)) b = spin (gvGlue η Sout σ) b from by
          unfold spin; rw [gvGlue_ovr_eq_off hsub η σ τ hb]]


theorem gv_bond_sum_diff_eq {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    (η : ConfigSpace (Site d)) (σ : {x // x ∈ Sout} → Bool) (τ : {x // x ∈ Sin} → Bool) :
    (∑ e ∈ gvBondTouch Sout, bond (gvGlue η Sout (gvOvr hsub σ τ)) e)
        - (∑ e ∈ gvBondTouch Sout, bond (gvGlue η Sout σ) e)
      = (∑ e ∈ gvBondTouch Sin, bond (gvGlue η Sout (gvOvr hsub σ τ)) e)
        - (∑ e ∈ gvBondTouch Sin, bond (gvGlue η Sout σ) e) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine (Finset.sum_subset (gv_bondTouch_subset hsub) (fun e heM heN => ?_)).symm
  have heE : e ∈ (hypercubicLattice d).edgeSet := gv_bondTouch_subset_edgeSet Sout e heM
  rw [gv_bond_glue_ovr_eq_of_notMem hsub η σ τ heE heN, sub_self]


theorem gv_spin_sum_diff_eq {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    (η : ConfigSpace (Site d)) (σ : {x // x ∈ Sout} → Bool) (τ : {x // x ∈ Sin} → Bool) :
    (∑ x ∈ Sout, spin (gvGlue η Sout (gvOvr hsub σ τ)) x)
        - (∑ x ∈ Sout, spin (gvGlue η Sout σ) x)
      = (∑ x ∈ Sin, spin (gvGlue η Sout (gvOvr hsub σ τ)) x)
        - (∑ x ∈ Sin, spin (gvGlue η Sout σ) x) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine (Finset.sum_subset hsub (fun x hxM hxN => ?_)).symm
  unfold spin
  rw [gvGlue_ovr_eq_off hsub η σ τ hxN, sub_self]


theorem gv_energy_decomp {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    (η : ConfigSpace (Site d)) (h : ℝ) (σ : {x // x ∈ Sout} → Bool) (τ : {x // x ∈ Sin} → Bool) :
    gvEnergy η Sout h σ + gvEnergy (gvGlue η Sout σ) Sin h τ
      = gvEnergy η Sout h (gvOvr hsub σ τ)
        + gvEnergy (gvGlue η Sout (gvOvr hsub σ τ)) Sin h (gvRes hsub σ) := by
  unfold gvEnergy
  rw [gvGlue_gvGlue_eq_gvGlue_ovr hsub η σ τ,
      gvGlue_gvGlue_eq_gvGlue_ovr hsub η (gvOvr hsub σ τ) (gvRes hsub σ),
      gvOvr_gvOvr_gvRes hsub σ τ]
  have hb := gv_bond_sum_diff_eq hsub η σ τ
  have hs := gv_spin_sum_diff_eq hsub η σ τ
  linear_combination hb + h * hs


theorem gv_weight_spec_symm {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    (η : ConfigSpace (Site d)) (β h : ℝ) (σ : {x // x ∈ Sout} → Bool) (τ : {x // x ∈ Sin} → Bool) :
    gvWeight η Sout β h σ * gvWeight (gvGlue η Sout σ) Sin β h τ
      = gvWeight η Sout β h (gvOvr hsub σ τ)
        * gvWeight (gvGlue η Sout (gvOvr hsub σ τ)) Sin β h (gvRes hsub σ) := by
  unfold gvWeight
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  have hE := gv_energy_decomp hsub η h σ τ
  ring_nf
  linear_combination (-β) * hE


theorem gv_fvWeight_eq_of_agree_off {Sin : Finset (Site d)} (β h : ℝ)
    {ζ₁ ζ₂ : ConfigSpace (Site d)} (hagree : ∀ x ∉ Sin, ζ₁ x = ζ₂ x)
    (τ : {x // x ∈ Sin} → Bool) :
    gvWeight ζ₁ Sin β h τ = gvWeight ζ₂ Sin β h τ := by
  unfold gvWeight gvEnergy
  have hglue : gvGlue ζ₁ Sin τ = gvGlue ζ₂ Sin τ := by
    funext x
    by_cases hx : x ∈ Sin
    · rw [gvGlue_mem _ _ _ hx, gvGlue_mem _ _ _ hx]
    · rw [gvGlue_not_mem _ _ _ hx, gvGlue_not_mem _ _ _ hx]; exact hagree x hx
  rw [hglue]

theorem gv_fvZ_eq_of_agree_off {Sin : Finset (Site d)} (β h : ℝ)
    {ζ₁ ζ₂ : ConfigSpace (Site d)} (hagree : ∀ x ∉ Sin, ζ₁ x = ζ₂ x) :
    gvZ ζ₁ Sin β h = gvZ ζ₂ Sin β h := by
  unfold gvZ
  exact Finset.sum_congr rfl (fun τ _ => gv_fvWeight_eq_of_agree_off β h hagree τ)


end Ising
end StatMech
