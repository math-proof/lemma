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
import Instance.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part2
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


theorem gvMeasure_real_eq (η : ConfigSpace (Site d)) (S : Finset (Site d)) (β h : ℝ)
    {A : Set (ConfigSpace (Site d))} (hA : MeasurableSet A) :
    (gvMeasure η S β h).real A
      = ∑ τ : {x // x ∈ S} → Bool,
          gvProb η S β h τ * (Set.indicator A (fun _ => (1 : ℝ)) (gvGlue η S τ)) := by
  unfold Measure.real
  rw [show (gvMeasure η S β h) A
        = ∑ τ : {x // x ∈ S} → Bool,
            (ENNReal.ofReal (gvProb η S β h τ) • Measure.dirac (gvGlue η S τ)) A from
      Measure.finsetSum_apply Finset.univ _ A]
  rw [ENNReal.toReal_sum (fun τ _ => by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ A))]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (gvProb_nonneg η S β h τ)]
  congr 1
  by_cases hmem : gvGlue η S τ ∈ A
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]; simp
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]; simp


theorem gvGlue_mono_interior (η : ConfigSpace (Site d)) (S : Finset (Site d))
    (τ τ' : {x // x ∈ S} → Bool) (h : τ ≤ τ') : gvGlue η S τ ≤ gvGlue η S τ' := by
  intro x
  by_cases hx : x ∈ S
  · rw [gvGlue_mem _ _ _ hx, gvGlue_mem _ _ _ hx]; exact h ⟨x, hx⟩
  · rw [gvGlue_not_mem _ _ _ hx, gvGlue_not_mem _ _ _ hx]


theorem gvGlue_mono_boundary (S : Finset (Site d)) (η η' : ConfigSpace (Site d)) (hle : η ≤ η')
    (τ : {x // x ∈ S} → Bool) : gvGlue η S τ ≤ gvGlue η' S τ := by
  intro x
  by_cases hx : x ∈ S
  · rw [gvGlue_mem _ _ _ hx, gvGlue_mem _ _ _ hx]
  · rw [gvGlue_not_mem _ _ _ hx, gvGlue_not_mem _ _ _ hx]; exact hle x


theorem gv_spin_glue_inf (S : Finset (Site d)) (η η' : ConfigSpace (Site d)) (hle : η ≤ η')
    (a b : {x // x ∈ S} → Bool) (x : Site d) :
    spin (gvGlue η S (a ⊓ b)) x = min (spin (gvGlue η S a) x) (spin (gvGlue η' S b) x) := by
  by_cases hx : x ∈ S
  · simp only [spin, gvGlue_mem _ _ _ hx, Pi.inf_apply]; exact spinB_inf _ _
  · simp only [spin, gvGlue_not_mem _ _ _ hx]
    conv_lhs => rw [show η x = η x ⊓ η' x from (inf_eq_left.mpr (hle x)).symm]
    exact spinB_inf _ _


theorem gv_spin_glue_sup (S : Finset (Site d)) (η η' : ConfigSpace (Site d)) (hle : η ≤ η')
    (a b : {x // x ∈ S} → Bool) (x : Site d) :
    spin (gvGlue η' S (a ⊔ b)) x = max (spin (gvGlue η S a) x) (spin (gvGlue η' S b) x) := by
  by_cases hx : x ∈ S
  · simp only [spin, gvGlue_mem _ _ _ hx, Pi.sup_apply]; exact spinB_sup _ _
  · simp only [spin, gvGlue_not_mem _ _ _ hx]
    conv_lhs => rw [show η' x = η x ⊔ η' x from (sup_eq_right.mpr (hle x)).symm]
    exact spinB_sup _ _


theorem gv_bond_glue_supermod (S : Finset (Site d)) (η η' : ConfigSpace (Site d)) (hle : η ≤ η')
    (a b : {x // x ∈ S} → Bool) (e : Sym2 (Site d)) :
    bond (gvGlue η S a) e + bond (gvGlue η' S b) e
      ≤ bond (gvGlue η S (a ⊓ b)) e + bond (gvGlue η' S (a ⊔ b)) e := by
  induction e using Sym2.inductionOn with
  | hf x y =>
    simp only [bond_mk]
    rw [gv_spin_glue_inf S η η' hle a b x, gv_spin_glue_inf S η η' hle a b y,
        gv_spin_glue_sup S η η' hle a b x, gv_spin_glue_sup S η η' hle a b y]
    exact prod_supermod _ _ _ _


theorem gv_spin_glue_add (S : Finset (Site d)) (η η' : ConfigSpace (Site d)) (hle : η ≤ η')
    (a b : {x // x ∈ S} → Bool) (x : Site d) :
    spin (gvGlue η S a) x + spin (gvGlue η' S b) x
      = spin (gvGlue η S (a ⊓ b)) x + spin (gvGlue η' S (a ⊔ b)) x := by
  rw [gv_spin_glue_inf S η η' hle a b x, gv_spin_glue_sup S η η' hle a b x]
  rcases le_total (spin (gvGlue η S a) x) (spin (gvGlue η' S b) x) with h | h
  · simp only [min_eq_left h, max_eq_right h]
  · simp only [min_eq_right h, max_eq_left h]; ring


theorem gv_fvEnergy_supermod (S : Finset (Site d)) (h : ℝ) (hh : 0 ≤ h)
    (η η' : ConfigSpace (Site d)) (hle : η ≤ η') (a b : {x // x ∈ S} → Bool) :
    gvEnergy η S h (a ⊓ b) + gvEnergy η' S h (a ⊔ b)
      ≤ gvEnergy η S h a + gvEnergy η' S h b := by
  unfold gvEnergy
  have hbond : ∑ e ∈ gvBondTouch S, bond (gvGlue η S a) e
        + ∑ e ∈ gvBondTouch S, bond (gvGlue η' S b) e
      ≤ ∑ e ∈ gvBondTouch S, bond (gvGlue η S (a ⊓ b)) e
        + ∑ e ∈ gvBondTouch S, bond (gvGlue η' S (a ⊔ b)) e := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun e _ => gv_bond_glue_supermod S η η' hle a b e)
  have hfield : ∑ x ∈ S, spin (gvGlue η S a) x + ∑ x ∈ S, spin (gvGlue η' S b) x
      = ∑ x ∈ S, spin (gvGlue η S (a ⊓ b)) x + ∑ x ∈ S, spin (gvGlue η' S (a ⊔ b)) x := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => gv_spin_glue_add S η η' hle a b x)
  have hfieldh : h * (∑ x ∈ S, spin (gvGlue η S a) x) + h * (∑ x ∈ S, spin (gvGlue η' S b) x)
      = h * (∑ x ∈ S, spin (gvGlue η S (a ⊓ b)) x)
        + h * (∑ x ∈ S, spin (gvGlue η' S (a ⊔ b)) x) := by rw [← mul_add, ← mul_add, hfield]
  linarith [hbond, hfieldh]


theorem gv_fvWeight_cross (S : Finset (Site d)) {β : ℝ} (hβ : 0 ≤ β) (h : ℝ) (hh : 0 ≤ h)
    (η η' : ConfigSpace (Site d)) (hle : η ≤ η') (a b : {x // x ∈ S} → Bool) :
    gvWeight η S β h a * gvWeight η' S β h b
      ≤ gvWeight η S β h (a ⊓ b) * gvWeight η' S β h (a ⊔ b) := by
  unfold gvWeight
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hc := gv_fvEnergy_supermod S h hh η η' hle a b
  nlinarith [mul_nonneg hβ (sub_nonneg.mpr hc)]


theorem gv_fvProb_cross (S : Finset (Site d)) {β : ℝ} (hβ : 0 ≤ β) (h : ℝ) (hh : 0 ≤ h)
    (η η' : ConfigSpace (Site d)) (hle : η ≤ η') (a b : {x // x ∈ S} → Bool) :
    gvProb η S β h a * gvProb η' S β h b
      ≤ gvProb η S β h (a ⊓ b) * gvProb η' S β h (a ⊔ b) := by
  have hZ1 : 0 < gvZ η S β h := gvZ_pos _ _ _ _
  have hZ2 : 0 < gvZ η' S β h := gvZ_pos _ _ _ _
  simp only [gvProb]
  rw [div_mul_div_comm, div_mul_div_comm]
  exact (div_le_div_iff_of_pos_right (mul_pos hZ1 hZ2)).mpr
    (gv_fvWeight_cross S hβ h hh η η' hle a b)


theorem gv_fvProb_dominates (S : Finset (Site d)) {β : ℝ} (hβ : 0 ≤ β) (h : ℝ) (hh : 0 ≤ h)
    (η η' : ConfigSpace (Site d)) (hle : η ≤ η')
    {A : Set (ConfigSpace {x // x ∈ S})} (hA : IsIncreasing A) :
    ∑ τ, A.indicator (fun _ => (1 : ℝ)) τ * gvProb η S β h τ
      ≤ ∑ τ, A.indicator (fun _ => (1 : ℝ)) τ * gvProb η' S β h τ :=
  holley_dominates (fun τ => gvProb_nonneg η S β h τ) (fun τ => gvProb_nonneg η' S β h τ)
    (by rw [gvProb_sum_eq_one, gvProb_sum_eq_one])
    (fun a b => gv_fvProb_cross S hβ h hh η η' hle a b) hA


theorem gvMeasure_dominated (S : Finset (Site d)) {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h)
    (η η' : ConfigSpace (Site d)) (hle : η ≤ η')
    {A : Set (ConfigSpace (Site d))} (hA : MeasurableSet A) (hAinc : IsIncreasing A) :
    (gvMeasure η S β h).real A ≤ (gvMeasure η' S β h).real A := by
  rw [gvMeasure_real_eq η S β h hA, gvMeasure_real_eq η' S β h hA]
  set A₁ : Set (ConfigSpace {x // x ∈ S}) := (fun τ => gvGlue η S τ) ⁻¹' A with hA1
  set A₂ : Set (ConfigSpace {x // x ∈ S}) := (fun τ => gvGlue η' S τ) ⁻¹' A with hA2
  have hreη : ∀ τ, Set.indicator A (fun _ => (1 : ℝ)) (gvGlue η S τ)
      = Set.indicator A₁ (fun _ => (1 : ℝ)) τ := by
    intro τ; by_cases hmem : gvGlue η S τ ∈ A
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show τ ∈ A₁ from hmem)]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (show τ ∉ A₁ from hmem)]
  have hreη' : ∀ τ, Set.indicator A (fun _ => (1 : ℝ)) (gvGlue η' S τ)
      = Set.indicator A₂ (fun _ => (1 : ℝ)) τ := by
    intro τ; by_cases hmem : gvGlue η' S τ ∈ A
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show τ ∈ A₂ from hmem)]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (show τ ∉ A₂ from hmem)]
  simp_rw [hreη, hreη']
  have hA1inc : IsIncreasing A₁ := fun τ τ' hτ hmem => hAinc (gvGlue_mono_interior η S τ τ' hτ) hmem
  have hsub : A₁ ⊆ A₂ := fun τ hmem => hAinc (gvGlue_mono_boundary S η η' hle τ) hmem
  calc ∑ τ, gvProb η S β h τ * Set.indicator A₁ (fun _ => (1 : ℝ)) τ
      = ∑ τ, Set.indicator A₁ (fun _ => (1 : ℝ)) τ * gvProb η S β h τ := by
        apply Finset.sum_congr rfl; intro τ _; ring
    _ ≤ ∑ τ, Set.indicator A₁ (fun _ => (1 : ℝ)) τ * gvProb η' S β h τ :=
        gv_fvProb_dominates S hβ h hh η η' hle hA1inc
    _ ≤ ∑ τ, Set.indicator A₂ (fun _ => (1 : ℝ)) τ * gvProb η' S β h τ := by
        apply Finset.sum_le_sum; intro τ _
        apply mul_le_mul_of_nonneg_right _ (gvProb_nonneg η' S β h τ)
        by_cases h1 : τ ∈ A₁
        · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (hsub h1)]
        · rw [Set.indicator_of_notMem h1]
          by_cases h2 : τ ∈ A₂
          · rw [Set.indicator_of_mem h2]; norm_num
          · rw [Set.indicator_of_notMem h2]
    _ = ∑ τ, gvProb η' S β h τ * Set.indicator A₂ (fun _ => (1 : ℝ)) τ := by
        apply Finset.sum_congr rfl; intro τ _; ring


theorem gv_le_plusField (η : ConfigSpace (Site d)) : η ≤ plusField d := by
  intro x; simp [plusField]


theorem gvMeasure_le_plusField (S : Finset (Site d)) {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h)
    (η : ConfigSpace (Site d)) {A : Set (ConfigSpace (Site d))} (hA : MeasurableSet A)
    (hAinc : IsIncreasing A) :
    (gvMeasure η S β h).real A ≤ (gvMeasure (plusField d) S β h).real A :=
  gvMeasure_dominated S hβ hh η (plusField d) (gv_le_plusField η) hA hAinc


end Ising
end StatMech
