/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRFiniteCoordinateBlocks.Part6
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductCore.Part6
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


theorem piFunctionalFamilyMax_cylinder_le_ae
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (f : (∀ e, S e) → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) :
    ∀ᵐ x ∂Measure.pi μ,
      piFunctionalFamilyMax (fun K => piCylinderEssInf μ f K) x ≤ f x := by
  have hall : ∀ K : Set E, ∀ᵐ x ∂Measure.pi μ,
      piCylinderEssInf μ f K x ≤ f x :=
    fun K => piCylinderEssInf_le_ae μ f hf hf0 K
  filter_upwards [ae_all_iff.mpr hall] with x hx
  unfold piFunctionalFamilyMax
  apply Finset.sup'_le
  intro K _
  exact hx K

theorem piFunctionalFamilyMax_cylinder_nonneg
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (f : (∀ e, S e) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (x : ∀ e, S e) :
    0 ≤ piFunctionalFamilyMax (fun K => piCylinderEssInf μ f K) x := by
  unfold piFunctionalFamilyMax
  let K : Set E := ∅
  calc
    0 ≤ piCylinderEssInf μ f K x :=
      piCylinderEssInf_nonneg μ f hf0 K x
    _ ≤ (Finset.univ : Finset (Set E)).sup'
        (Finset.univ_nonempty : (Finset.univ : Finset (Set E)).Nonempty)
        (fun L => piCylinderEssInf μ f L x) :=
      Finset.le_sup' (fun L : Set E => piCylinderEssInf μ f L x)
        (Finset.mem_univ K)


theorem functionalBKR_generalProduct_of_familyBKR
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (hBKR : HasMeasurableFunctionalBKR μ)
    (f g : (∀ e, S e) → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    (∫⁻ x, ENNReal.ofReal (piFunctionalDisjointEssMax μ f g x)
        ∂Measure.pi μ) ≤
      (∫⁻ x, ENNReal.ofReal (f x) ∂Measure.pi μ) *
        ∫⁻ x, ENNReal.ofReal (g x) ∂Measure.pi μ := by
  let F : Set E → (∀ e, S e) → ℝ := fun K => piCylinderEssInf μ f K
  let G : Set E → (∀ e, S e) → ℝ := fun K => piCylinderEssInf μ g K
  have hcore := hBKR F G
    (fun K => measurable_piCylinderEssInf μ f hf hf0 K)
    (fun K => measurable_piCylinderEssInf μ g hg hg0 K)
    (fun K x => piCylinderEssInf_nonneg μ f hf0 K x)
    (fun K x => piCylinderEssInf_nonneg μ g hg0 K x)
    (fun K _ _ hxy => piCylinderEssInf_eq_of_piAgreeOn μ f K hxy)
    (fun K _ _ hxy => piCylinderEssInf_eq_of_piAgreeOn μ g K hxy)
  have hF := piFunctionalFamilyMax_cylinder_le_ae μ f hf hf0
  have hG := piFunctionalFamilyMax_cylinder_le_ae μ g hg hg0
  have hFint : (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax F x)
      ∂Measure.pi μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂Measure.pi μ := by
    apply lintegral_mono_ae
    filter_upwards [hF] with x hx
    exact ENNReal.ofReal_le_ofReal hx
  have hGint : (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax G x)
      ∂Measure.pi μ) ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂Measure.pi μ := by
    apply lintegral_mono_ae
    filter_upwards [hG] with x hx
    exact ENNReal.ofReal_le_ofReal hx
  calc
    (∫⁻ x, ENNReal.ofReal (piFunctionalDisjointEssMax μ f g x)
        ∂Measure.pi μ) =
        ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyDisjointMax F G x)
          ∂Measure.pi μ := by rfl
    _ ≤ (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax F x) ∂Measure.pi μ) *
          ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax G x) ∂Measure.pi μ := hcore
    _ ≤ (∫⁻ x, ENNReal.ofReal (f x) ∂Measure.pi μ) *
          ∫⁻ x, ENNReal.ofReal (g x) ∂Measure.pi μ :=
      mul_le_mul hFint hGint (by positivity) (by positivity)


theorem dualFunctionalBKR_generalProduct_of_familyBKR
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (hBKR : HasMeasurableDualFunctionalBKR μ)
    (f g : (∀ e, S e) → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    (∫⁻ p, ENNReal.ofReal
        (piFunctionalDisjointEssMaxAt μ f g p.1 p.2)
        ∂(Measure.pi μ).prod (Measure.pi μ)) ≤
      ∫⁻ x, ENNReal.ofReal (f x * g x) ∂Measure.pi μ := by
  let F : Set E → (∀ e, S e) → ℝ := fun K => piCylinderEssInf μ f K
  let G : Set E → (∀ e, S e) → ℝ := fun K => piCylinderEssInf μ g K
  have hcore := hBKR F G
    (fun K => measurable_piCylinderEssInf μ f hf hf0 K)
    (fun K => measurable_piCylinderEssInf μ g hg hg0 K)
    (fun K x => piCylinderEssInf_nonneg μ f hf0 K x)
    (fun K x => piCylinderEssInf_nonneg μ g hg0 K x)
    (fun K _ _ hxy => piCylinderEssInf_eq_of_piAgreeOn μ f K hxy)
    (fun K _ _ hxy => piCylinderEssInf_eq_of_piAgreeOn μ g K hxy)
  have hF := piFunctionalFamilyMax_cylinder_le_ae μ f hf hf0
  have hG := piFunctionalFamilyMax_cylinder_le_ae μ g hg hg0
  calc
    (∫⁻ p, ENNReal.ofReal
        (piFunctionalDisjointEssMaxAt μ f g p.1 p.2)
        ∂(Measure.pi μ).prod (Measure.pi μ)) =
        ∫⁻ p, ENNReal.ofReal
          (piFunctionalFamilyDisjointMaxAt F G p.1 p.2)
          ∂(Measure.pi μ).prod (Measure.pi μ) := by rfl
    _ ≤ ∫⁻ x, ENNReal.ofReal
          (piFunctionalFamilyMax F x * piFunctionalFamilyMax G x)
          ∂Measure.pi μ := hcore
    _ ≤ ∫⁻ x, ENNReal.ofReal (f x * g x) ∂Measure.pi μ := by
      apply lintegral_mono_ae
      filter_upwards [hF, hG] with x hxF hxG
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul hxF hxG
        (piFunctionalFamilyMax_cylinder_nonneg μ g hg0 x)
        (hf0 x)


theorem piFunctionalFamilyMax_nonneg
    (F : Set E → (∀ e, S e) → ℝ) (hF0 : ∀ K x, 0 ≤ F K x)
    (x : ∀ e, S e) :
    0 ≤ piFunctionalFamilyMax F x := by
  unfold piFunctionalFamilyMax
  let K : Set E := ∅
  calc
    0 ≤ F K x := hF0 K x
    _ ≤ (Finset.univ : Finset (Set E)).sup'
        (Finset.univ_nonempty : (Finset.univ : Finset (Set E)).Nonempty)
        (fun L => F L x) :=
      Finset.le_sup' (fun L : Set E => F L x) (Finset.mem_univ K)

theorem familyMember_le_cylinderMin_familyMax
    (F : Set E → StatMech.ConfigSpace E → ℝ)
    (hF : ∀ K, PiDependsOn K (F K))
    (K : Set E) (omega : StatMech.ConfigSpace E) :
    F K omega ≤ cylinderMin (piFunctionalFamilyMax F) K omega := by
  unfold cylinderMin
  apply Finset.le_inf'
  intro eta heta
  have hagree : piAgreeOn K omega eta := by
    intro e he
    exact (mem_agreementFiber.mp heta e he).symm
  calc
    F K omega = F K eta := hF K hagree
    _ ≤ piFunctionalFamilyMax F eta := by
      unfold piFunctionalFamilyMax
      exact Finset.le_sup' (fun L : Set E => F L eta) (Finset.mem_univ K)

theorem piFunctionalFamilyDisjointMaxAt_le
    (F G : Set E → StatMech.ConfigSpace E → ℝ)
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hF : ∀ K, PiDependsOn K (F K))
    (hG : ∀ K, PiDependsOn K (G K))
    (omega eta : StatMech.ConfigSpace E) :
    piFunctionalFamilyDisjointMaxAt F G omega eta ≤
      functionalDisjointMaxAt (piFunctionalFamilyMax F)
        (piFunctionalFamilyMax G) omega eta := by
  unfold piFunctionalFamilyDisjointMaxAt
  apply Finset.sup'_le
  intro pair hpair
  have hleft : F pair.1 omega ≤
      cylinderMin (piFunctionalFamilyMax F) pair.1 omega :=
    familyMember_le_cylinderMin_familyMax F hF pair.1 omega
  have hright : G pair.2 eta ≤
      cylinderMin (piFunctionalFamilyMax G) pair.2 eta :=
    familyMember_le_cylinderMin_familyMax G hG pair.2 eta
  calc
    F pair.1 omega * G pair.2 eta ≤
        cylinderMin (piFunctionalFamilyMax F) pair.1 omega *
          cylinderMin (piFunctionalFamilyMax G) pair.2 eta :=
      mul_le_mul hleft hright (hG0 pair.2 eta)
        (cylinderMin_nonneg (piFunctionalFamilyMax_nonneg F hF0) pair.1 omega)
    _ ≤ functionalDisjointMaxAt (piFunctionalFamilyMax F)
          (piFunctionalFamilyMax G) omega eta := by
      unfold functionalDisjointMaxAt
      exact Finset.le_sup'
        (fun p : Set E × Set E =>
          cylinderMin (piFunctionalFamilyMax F) p.1 omega *
            cylinderMin (piFunctionalFamilyMax G) p.2 eta) hpair

theorem functionalFamilyBKR_real
    (phi : E → Bool → ℝ)
    (hphi0 : ∀ e b, 0 ≤ phi e b)
    (hphi1 : ∀ e, phi e false + phi e true = 1)
    (F G : Set E → StatMech.ConfigSpace E → ℝ)
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hF : ∀ K, PiDependsOn K (F K))
    (hG : ∀ K, PiDependsOn K (G K)) :
    productExpectation phi (piFunctionalFamilyDisjointMax F G) ≤
      productExpectation phi (piFunctionalFamilyMax F) *
        productExpectation phi (piFunctionalFamilyMax G) := by
  calc
    productExpectation phi (piFunctionalFamilyDisjointMax F G) ≤
        productExpectation phi
          (functionalDisjointMax (piFunctionalFamilyMax F)
            (piFunctionalFamilyMax G)) := by
      unfold productExpectation
      apply Finset.sum_le_sum
      intro omega _
      exact mul_le_mul_of_nonneg_left
        (piFunctionalFamilyDisjointMaxAt_le F G hF0 hG0 hF hG omega omega)
        (pweight_nonneg hphi0 omega)
    _ ≤ productExpectation phi (piFunctionalFamilyMax F) *
          productExpectation phi (piFunctionalFamilyMax G) :=
      functionalBKR_real phi hphi0 hphi1 _ _
        (piFunctionalFamilyMax_nonneg F hF0)
        (piFunctionalFamilyMax_nonneg G hG0)

theorem dualFunctionalFamilyBKR_real
    (phi : E → Bool → ℝ)
    (hphi0 : ∀ e b, 0 ≤ phi e b)
    (hphi1 : ∀ e, phi e false + phi e true = 1)
    (F G : Set E → StatMech.ConfigSpace E → ℝ)
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hF : ∀ K, PiDependsOn K (F K))
    (hG : ∀ K, PiDependsOn K (G K)) :
    dualProductExpectation phi (fun p =>
        piFunctionalFamilyDisjointMaxAt F G p.1 p.2) ≤
      productExpectation phi (fun x =>
        piFunctionalFamilyMax F x * piFunctionalFamilyMax G x) := by
  calc
    dualProductExpectation phi (fun p =>
        piFunctionalFamilyDisjointMaxAt F G p.1 p.2) ≤
        dualProductExpectation phi (fun p =>
          functionalDisjointMaxAt (piFunctionalFamilyMax F)
            (piFunctionalFamilyMax G) p.1 p.2) := by
      unfold dualProductExpectation
      apply Finset.sum_le_sum
      intro omega _
      apply Finset.sum_le_sum
      intro eta _
      exact mul_le_mul_of_nonneg_left
        (piFunctionalFamilyDisjointMaxAt_le F G hF0 hG0 hF hG omega eta)
        (mul_nonneg (pweight_nonneg hphi0 omega) (pweight_nonneg hphi0 eta))
    _ ≤ productExpectation phi (fun x =>
          piFunctionalFamilyMax F x * piFunctionalFamilyMax G x) :=
      dualFunctionalBKR_real phi hphi0 hphi1 _ _
        (piFunctionalFamilyMax_nonneg F hF0)
        (piFunctionalFamilyMax_nonneg G hG0)

theorem productExpectation_fin_cons {n : ℕ}
    (phi : Fin (n + 1) → Bool → ℝ)
    (H : (Fin (n + 1) → Bool) → ℝ) :
    productExpectation phi H =
      ∑ b : Bool, phi 0 b *
        productExpectation (fun i b => phi i.succ b)
          (fun eta => H (Fin.cons b eta)) := by
  unfold productExpectation pweight
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro eta _
  have hcons :
      (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)) (b, eta) =
        Fin.cons b eta := by
    rfl
  rw [hcons]
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring


end StatMech.FrontierA
