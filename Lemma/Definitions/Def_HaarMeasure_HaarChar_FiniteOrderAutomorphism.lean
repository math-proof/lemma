import Mathlib

set_option autoImplicit false

open MeasureTheory.Measure
open scoped NNReal

namespace MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

private lemma nnreal_eq_one_of_pow_eq_one {x : ℝ≥0} {n : ℕ} (hn : n ≠ 0) (h : x ^ n = 1) :
    x = 1 := by
  rcases lt_trichotomy x 1 with hlt | heq | hgt
  · exact absurd h (pow_lt_one₀ zero_le hlt hn).ne
  · exact heq
  · exact absurd h (one_lt_pow₀ hgt hn).ne'

@[to_additive]
lemma exists_continuousMulEquiv_iterate_mulEquivHaarChar (φ : G ≃ₜ* G) (n : ℕ) :
    ∃ ψ : G ≃ₜ* G, ⇑ψ = (⇑φ)^[n] ∧ mulEquivHaarChar ψ = mulEquivHaarChar φ ^ n := by
  induction n with
  | zero =>
      refine ⟨ContinuousMulEquiv.refl G, funext fun g => ?_, ?_⟩
      · exact (ContinuousMulEquiv.refl_apply G g).trans (Function.iterate_zero_apply (⇑φ) g).symm
      · exact (mulEquivHaarChar_refl (G := G)).trans (pow_zero _).symm
  | succ n ih =>
      obtain ⟨ψ, hcoe, hchar⟩ := ih
      refine ⟨ψ.trans φ, funext fun g => ?_, ?_⟩
      · exact (ContinuousMulEquiv.trans_apply ψ φ g).trans
          ((congrArg (⇑φ) (congrFun hcoe g)).trans (Function.iterate_succ_apply' (⇑φ) n g).symm)
      · calc mulEquivHaarChar (ψ.trans φ)
              = mulEquivHaarChar ψ * mulEquivHaarChar φ := mulEquivHaarChar_trans
          _ = mulEquivHaarChar φ ^ n * mulEquivHaarChar φ := by rw [hchar]
          _ = mulEquivHaarChar φ ^ (n + 1) := (pow_succ _ n).symm

@[to_additive addEquivAddHaarChar_pow_eq_one_of_iterate_eq_id]
lemma mulEquivHaarChar_pow_eq_one_of_iterate_eq_id (φ : G ≃ₜ* G) {ℓ : ℕ}
    (h : ∀ g, (⇑φ)^[ℓ] g = g) : mulEquivHaarChar φ ^ ℓ = 1 := by
  obtain ⟨ψ, hcoe, hchar⟩ := exists_continuousMulEquiv_iterate_mulEquivHaarChar φ ℓ
  have hψ : ψ = ContinuousMulEquiv.refl G := by
    refine ContinuousMulEquiv.ext fun g => ?_
    rw [ContinuousMulEquiv.refl_apply]
    exact (congrFun hcoe g).trans (h g)
  rw [← hchar, hψ, mulEquivHaarChar_refl]

@[to_additive addEquivAddHaarChar_eq_one_of_iterate_eq_id]
theorem mulEquivHaarChar_eq_one_of_iterate_eq_id (φ : G ≃ₜ* G) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (h : ∀ g, (⇑φ)^[ℓ] g = g) : mulEquivHaarChar φ = 1 :=
  nnreal_eq_one_of_pow_eq_one hℓ (mulEquivHaarChar_pow_eq_one_of_iterate_eq_id φ h)

@[to_additive addEquivAddHaarChar_symm_eq_one_of_iterate_eq_id]
theorem mulEquivHaarChar_symm_eq_one_of_iterate_eq_id (φ : G ≃ₜ* G) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (h : ∀ g, (⇑φ)^[ℓ] g = g) : mulEquivHaarChar φ.symm = 1 := by
  rw [mulEquivHaarChar_symm, mulEquivHaarChar_eq_one_of_iterate_eq_id φ hℓ h, inv_one]

@[to_additive]
theorem map_haar_eq_self_of_iterate_eq_id (μ : Measure G) [IsHaarMeasure μ] [Regular μ]
    (φ : G ≃ₜ* G) {ℓ : ℕ} (hℓ : ℓ ≠ 0) (h : ∀ g, (⇑φ)^[ℓ] g = g) :
    μ.map φ = μ := by
  have h1 := mulEquivHaarChar_smul_map μ φ
  rwa [mulEquivHaarChar_eq_one_of_iterate_eq_id φ hℓ h, one_smul] at h1

@[to_additive]
theorem map_haar_symm_eq_self_of_iterate_eq_id (μ : Measure G) [IsHaarMeasure μ] [Regular μ]
    (φ : G ≃ₜ* G) {ℓ : ℕ} (hℓ : ℓ ≠ 0) (h : ∀ g, (⇑φ)^[ℓ] g = g) :
    μ.map φ.symm = μ := by
  have h1 := mulEquivHaarChar_smul_map μ φ.symm
  rwa [mulEquivHaarChar_symm_eq_one_of_iterate_eq_id φ hℓ h, one_smul] at h1

@[to_additive]
theorem measurePreserving_haar_of_iterate_eq_id (μ : Measure G) [IsHaarMeasure μ] [Regular μ]
    (φ : G ≃ₜ* G) {ℓ : ℕ} (hℓ : ℓ ≠ 0) (h : ∀ g, (⇑φ)^[ℓ] g = g) :
    MeasurePreserving (⇑φ) μ μ :=
  ⟨(map_continuous φ).measurable, map_haar_eq_self_of_iterate_eq_id μ φ hℓ h⟩

@[to_additive]
theorem measurePreserving_haar_symm_of_iterate_eq_id (μ : Measure G) [IsHaarMeasure μ]
    [Regular μ] (φ : G ≃ₜ* G) {ℓ : ℕ} (hℓ : ℓ ≠ 0) (h : ∀ g, (⇑φ)^[ℓ] g = g) :
    MeasurePreserving (⇑φ.symm) μ μ :=
  ⟨(map_continuous φ.symm).measurable, map_haar_symm_eq_self_of_iterate_eq_id μ φ hℓ h⟩

@[to_additive]
theorem measure_preimage_haar_eq_of_iterate_eq_id (μ : Measure G) [IsHaarMeasure μ] [Regular μ]
    (φ : G ≃ₜ* G) {ℓ : ℕ} (hℓ : ℓ ≠ 0) (h : ∀ g, (⇑φ)^[ℓ] g = g) (X : Set G) :
    μ (⇑φ ⁻¹' X) = μ X := by
  have h1 := mulEquivHaarChar_smul_preimage μ (X := X) φ
  rwa [mulEquivHaarChar_eq_one_of_iterate_eq_id φ hℓ h, one_smul] at h1

@[to_additive]
theorem integral_comp_haar_eq_of_iterate_eq_id (μ : Measure G) [IsHaarMeasure μ] [Regular μ]
    (φ : G ≃ₜ* G) {ℓ : ℕ} (hℓ : ℓ ≠ 0) (h : ∀ g, (⇑φ)^[ℓ] g = g) (f : G → ℝ) :
    ∫ g, f (φ g) ∂μ = ∫ g, f g ∂μ := by
  have hemb : MeasurableEmbedding (⇑φ) := φ.toHomeomorph.measurableEmbedding
  exact (measurePreserving_haar_of_iterate_eq_id μ φ hℓ h).integral_comp hemb f

section Stability

omit [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] in

@[to_additive]
theorem _root_.ContinuousMulEquiv.preimage_symm_eq_of_preimage_eq (φ : G ≃ₜ* G) {D : Set G}
    (hstable : ⇑φ ⁻¹' D = D) : ⇑φ.symm ⁻¹' D = D := by
  conv_lhs => rw [← hstable]
  ext g
  simp [ContinuousMulEquiv.apply_symm_apply]

omit [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] in

@[to_additive]
theorem _root_.ContinuousMulEquiv.preimage_eq_of_image_eq (φ : G ≃ₜ* G) {D : Set G}
    (hstable : ⇑φ '' D = D) : ⇑φ ⁻¹' D = D := by
  conv_lhs => rw [← hstable]
  rw [Set.preimage_image_eq D φ.injective]

end Stability

section Restricted

omit [IsTopologicalGroup G] [LocallyCompactSpace G] in

@[to_additive addEquiv_measurePreserving_restrict_of_map_eq_self]
theorem measurePreserving_restrict_of_map_eq_self (μ : Measure G) (φ : G ≃ₜ* G)
    (hmap : μ.map φ = μ) {D : Set G} (hD : MeasurableSet D) (hstable : ⇑φ ⁻¹' D = D) :
    MeasurePreserving (⇑φ) (μ.restrict D) (μ.restrict D) := by
  refine ⟨(map_continuous φ).measurable, ?_⟩
  conv_lhs => rw [← hstable]
  rw [← Measure.restrict_map (map_continuous φ).measurable hD, hmap]

@[to_additive]
theorem measurePreserving_restrict_haar_of_iterate_eq_id (μ : Measure G) [IsHaarMeasure μ]
    [Regular μ] (φ : G ≃ₜ* G) {ℓ : ℕ} (hℓ : ℓ ≠ 0) (h : ∀ g, (⇑φ)^[ℓ] g = g)
    {D : Set G} (hD : MeasurableSet D) (hstable : ⇑φ ⁻¹' D = D) :
    MeasurePreserving (⇑φ) (μ.restrict D) (μ.restrict D) :=
  measurePreserving_restrict_of_map_eq_self μ φ
    (map_haar_eq_self_of_iterate_eq_id μ φ hℓ h) hD hstable

@[to_additive]
theorem measurePreserving_restrict_haar_symm_of_iterate_eq_id (μ : Measure G) [IsHaarMeasure μ]
    [Regular μ] (φ : G ≃ₜ* G) {ℓ : ℕ} (hℓ : ℓ ≠ 0) (h : ∀ g, (⇑φ)^[ℓ] g = g)
    {D : Set G} (hD : MeasurableSet D) (hstable : ⇑φ ⁻¹' D = D) :
    MeasurePreserving (⇑φ.symm) (μ.restrict D) (μ.restrict D) :=
  measurePreserving_restrict_of_map_eq_self μ φ.symm
    (map_haar_symm_eq_self_of_iterate_eq_id μ φ hℓ h) hD
    (φ.preimage_symm_eq_of_preimage_eq hstable)

end Restricted

section MulEquivCurrency

@[to_additive]
theorem mulEquiv_measurePreserving_restrict_of_iterate_eq_id (μ : Measure G) [IsHaarMeasure μ]
    [Regular μ] (ψ : G ≃* G) (hc : Continuous ψ) (hc' : Continuous ψ.symm) {ℓ : ℕ}
    (hℓ : ℓ ≠ 0) (h : ∀ g, (fun x => ψ x)^[ℓ] g = g) {D : Set G} (hD : MeasurableSet D)
    (hstable : (fun x => ψ x) ⁻¹' D = D) :
    MeasurePreserving (fun x => ψ x) (μ.restrict D) (μ.restrict D) :=
  measurePreserving_restrict_haar_of_iterate_eq_id μ
    ({ ψ with continuous_toFun := hc, continuous_invFun := hc' } : G ≃ₜ* G) hℓ h hD hstable

@[to_additive]
theorem mulEquiv_measurePreserving_restrict_symm_of_iterate_eq_id (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] (ψ : G ≃* G) (hc : Continuous ψ) (hc' : Continuous ψ.symm)
    {ℓ : ℕ} (hℓ : ℓ ≠ 0) (h : ∀ g, (fun x => ψ x)^[ℓ] g = g) {D : Set G} (hD : MeasurableSet D)
    (hstable : (fun x => ψ x) ⁻¹' D = D) :
    MeasurePreserving (fun x => ψ.symm x) (μ.restrict D) (μ.restrict D) :=
  measurePreserving_restrict_haar_symm_of_iterate_eq_id μ
    ({ ψ with continuous_toFun := hc, continuous_invFun := hc' } : G ≃ₜ* G) hℓ h hD hstable

@[to_additive]
theorem mulEquiv_measurePreserving_restrict_pair_of_iterate_eq_id (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] (ψ : G ≃* G) (hc : Continuous ψ) (hc' : Continuous ψ.symm)
    {ℓ : ℕ} (hℓ : ℓ ≠ 0) (h : ∀ g, (fun x => ψ x)^[ℓ] g = g) {D : Set G} (hD : MeasurableSet D)
    (hstable : (fun x => ψ x) ⁻¹' D = D) :
    MeasurePreserving (fun x => ψ.symm x) (μ.restrict D) (μ.restrict D) ∧
      MeasurePreserving (fun x => ψ x) (μ.restrict D) (μ.restrict D) :=
  ⟨mulEquiv_measurePreserving_restrict_symm_of_iterate_eq_id μ ψ hc hc' hℓ h hD hstable,
    mulEquiv_measurePreserving_restrict_of_iterate_eq_id μ ψ hc hc' hℓ h hD hstable⟩

end MulEquivCurrency

end MeasureTheory

namespace FLT.HaarFiniteOrderGates

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

section Inversion

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

@[to_additive

                                                   ]
def invContinuousMulEquiv : G ≃ₜ* G where
  toFun g := g⁻¹
  invFun g := g⁻¹
  left_inv g := inv_inv g
  right_inv g := inv_inv g
  map_mul' a b := mul_inv a b
  continuous_toFun := continuous_inv
  continuous_invFun := continuous_inv

omit [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] in
@[to_additive (attr := simp)]
lemma invContinuousMulEquiv_apply (g : G) : invContinuousMulEquiv G g = g⁻¹ := rfl

omit [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] in
@[to_additive]
lemma invContinuousMulEquiv_coe : ⇑(invContinuousMulEquiv G) = fun g : G => g⁻¹ := rfl

omit [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] in

@[to_additive]
lemma invContinuousMulEquiv_iterate_two (g : G) :
    (⇑(invContinuousMulEquiv G))^[2] g = g := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply, Function.iterate_one]
  simp

variable {G}

@[to_additive]
theorem gate_map_inv_eq_self (μ : Measure G) [IsHaarMeasure μ] [Regular μ] :
    μ.map (fun g : G => g⁻¹) = μ := by
  have h := MeasureTheory.map_haar_eq_self_of_iterate_eq_id μ (invContinuousMulEquiv G)
    (ℓ := 2) (by norm_num) (invContinuousMulEquiv_iterate_two G)
  rwa [invContinuousMulEquiv_coe] at h

@[to_additive]
theorem gate_inv_two_routes (μ : Measure G) [IsHaarMeasure μ] [Regular μ] :
    μ.map (fun g : G => g⁻¹) = μ ∧ Measure.map Inv.inv μ = μ :=
  ⟨gate_map_inv_eq_self μ, Measure.map_inv_eq_self μ⟩

end Inversion

section RealNegation

theorem gate_real_map_neg_volume :
    (volume : Measure ℝ).map (fun x : ℝ => -x) = volume :=
  gate_map_neg_eq_self (volume : Measure ℝ)

theorem gate_real_two_routes :
    (volume : Measure ℝ).map (fun x : ℝ => -x) = volume ∧
      Measure.map Neg.neg (volume : Measure ℝ) = volume :=
  ⟨gate_real_map_neg_volume, Measure.map_neg_eq_self (volume : Measure ℝ)⟩

theorem gate_neg_preimage_Icc :
    (fun x : ℝ => -x) ⁻¹' Set.Icc (-1 : ℝ) 1 = Set.Icc (-1 : ℝ) 1 := by
  ext x
  simp only [Set.mem_preimage, Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

theorem gate_real_neg_measurePreserving_restrict_Icc :
    MeasurePreserving (fun x : ℝ => -x)
      ((volume : Measure ℝ).restrict (Set.Icc (-1 : ℝ) 1))
      ((volume : Measure ℝ).restrict (Set.Icc (-1 : ℝ) 1)) := by
  have h := MeasureTheory.measurePreserving_restrict_addHaar_of_iterate_eq_id
    (volume : Measure ℝ) (negContinuousAddEquiv ℝ) (ℓ := 2) (by norm_num)
    (negContinuousAddEquiv_iterate_two ℝ) (D := Set.Icc (-1 : ℝ) 1) measurableSet_Icc
    (by rw [negContinuousAddEquiv_coe]; exact gate_neg_preimage_Icc)
  rwa [negContinuousAddEquiv_coe] at h

end RealNegation

section Separation

noncomputable def doublingContinuousAddEquiv : ℝ ≃ₜ+ ℝ where
  toFun x := 2 * x
  invFun x := 2⁻¹ * x
  left_inv x := by norm_num [← mul_assoc]
  right_inv x := by norm_num [← mul_assoc]
  map_add' a b := mul_add 2 a b
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] lemma doublingContinuousAddEquiv_apply (x : ℝ) :
    doublingContinuousAddEquiv x = 2 * x := rfl

lemma gate_doubling_preimage_Icc :
    (⇑doublingContinuousAddEquiv) ⁻¹' Set.Icc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 2⁻¹ := by
  ext x
  simp only [Set.mem_preimage, doublingContinuousAddEquiv_apply, Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

theorem gate_doubling_addHaarChar_ne_one :
    MeasureTheory.addEquivAddHaarChar doublingContinuousAddEquiv ≠ 1 := by
  intro hc
  have hpre := MeasureTheory.addEquivAddHaarChar_smul_preimage (volume : Measure ℝ)
    (X := Set.Icc (0 : ℝ) 1) doublingContinuousAddEquiv
  rw [hc, one_smul, gate_doubling_preimage_Icc, Real.volume_Icc, Real.volume_Icc,
    ENNReal.ofReal_eq_ofReal_iff (p := 2⁻¹ - 0) (q := 1 - 0) (by norm_num) (by norm_num)] at hpre
  norm_num at hpre

theorem gate_iterate_zero_trivial (A : Type*) [AddGroup A] [TopologicalSpace A]
    (φ : A ≃ₜ+ A) (a : A) : (⇑φ)^[0] a = a :=
  Function.iterate_zero_apply (⇑φ) a

end Separation

end FLT.HaarFiniteOrderGates

/--
info: 'MeasureTheory.mulEquivHaarChar_eq_one_of_iterate_eq_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.mulEquivHaarChar_eq_one_of_iterate_eq_id

/--
info: 'MeasureTheory.addEquivAddHaarChar_eq_one_of_iterate_eq_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.addEquivAddHaarChar_eq_one_of_iterate_eq_id

/--
info: 'MeasureTheory.map_haar_eq_self_of_iterate_eq_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.map_haar_eq_self_of_iterate_eq_id

/--
info: 'MeasureTheory.map_addHaar_eq_self_of_iterate_eq_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.map_addHaar_eq_self_of_iterate_eq_id

/--
info: 'MeasureTheory.measurePreserving_haar_of_iterate_eq_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.measurePreserving_haar_of_iterate_eq_id

/--
info: 'MeasureTheory.measure_preimage_haar_eq_of_iterate_eq_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.measure_preimage_haar_eq_of_iterate_eq_id

/--
info: 'MeasureTheory.integral_comp_haar_eq_of_iterate_eq_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.integral_comp_haar_eq_of_iterate_eq_id

/--
info: 'MeasureTheory.measurePreserving_restrict_of_map_eq_self' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.measurePreserving_restrict_of_map_eq_self

/--
info: 'MeasureTheory.measurePreserving_restrict_haar_of_iterate_eq_id' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.measurePreserving_restrict_haar_of_iterate_eq_id

/--
info: 'MeasureTheory.measurePreserving_restrict_haar_symm_of_iterate_eq_id' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.measurePreserving_restrict_haar_symm_of_iterate_eq_id

/--
info: 'MeasureTheory.mulEquiv_measurePreserving_restrict_pair_of_iterate_eq_id' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.mulEquiv_measurePreserving_restrict_pair_of_iterate_eq_id

/--
info: 'MeasureTheory.addEquiv_measurePreserving_restrict_pair_of_iterate_eq_id' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.addEquiv_measurePreserving_restrict_pair_of_iterate_eq_id

/--
info: 'FLT.HaarFiniteOrderGates.gate_inv_two_routes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLT.HaarFiniteOrderGates.gate_inv_two_routes

/--
info: 'FLT.HaarFiniteOrderGates.gate_real_two_routes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLT.HaarFiniteOrderGates.gate_real_two_routes

/--
info: 'FLT.HaarFiniteOrderGates.gate_real_neg_measurePreserving_restrict_Icc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FLT.HaarFiniteOrderGates.gate_real_neg_measurePreserving_restrict_Icc

/--
info: 'FLT.HaarFiniteOrderGates.gate_doubling_addHaarChar_ne_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLT.HaarFiniteOrderGates.gate_doubling_addHaarChar_ne_one
