import Theorem.Analysis.MeasureTheory.Section_1_3_3.Part2
import Def.Analysis.MeasureTheory.Section_1_3_4.Part5


theorem L1.dist_eq {d:ℕ} (f g: EuclideanSpace' d → ℂ) (hf: ComplexAbsolutelyIntegrable f) (hg: ComplexAbsolutelyIntegrable g) : dist hf.toL1 hg.toL1 = (hf.sub hg).norm := by
  simp only [ComplexAbsolutelyIntegrable.toL1]
  rw [SeparationQuotient.dist_mk, dist_eq_norm]
  simp only [ComplexAbsolutelyIntegrable.norm, UnsignedAbsolutelyIntegrable.integ, Norm.norm]; rfl

theorem L1.dist_eq_zero {d:ℕ} (f g: EuclideanSpace' d → ℂ) (hf: ComplexAbsolutelyIntegrable f) (hg: ComplexAbsolutelyIntegrable g) : dist hf.toL1 hg.toL1 = 0 ↔ AlmostEverywhereEqual f g := by
  rw [L1.dist_eq]
  simp only [ComplexAbsolutelyIntegrable.norm, UnsignedAbsolutelyIntegrable.integ]
  rw [EReal.toReal_eq_zero_iff]
  -- Eliminate ⊤ and ⊥ cases
  have h_finite : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) < ⊤ := (hf.sub hg).2
  have h_nonneg : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≥ 0 :=
    UnsignedLebesgueIntegral.nonneg (hf.sub hg).abs.1
  have h_ne_top : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≠ ⊤ := ne_of_lt h_finite
  have h_ne_bot : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≠ ⊥ := by
    intro h_eq_bot
    rw [h_eq_bot] at h_nonneg
    exact not_le.mpr EReal.bot_lt_zero h_nonneg
  simp only [h_ne_top, h_ne_bot, or_false]
  -- Now goal: UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) = 0 ↔ AlmostEverywhereEqual f g
  have h_meas : UnsignedMeasurable (EReal.abs_fun (f - g)) := (hf.sub hg).abs.1
  rw [show UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) = h_meas.integ from rfl]
  rw [UnsignedLebesgueIntegral.eq_zero_aeZero h_meas]
  -- Goal: AlmostAlways (fun x ↦ EReal.abs_fun (f - g) x = 0) ↔ AlmostEverywhereEqual f g
  unfold AlmostEverywhereEqual AlmostAlways
  -- Goal: IsNull {x | ¬EReal.abs_fun (f - g) x = 0} ↔ IsNull {x | ¬f x = g x}
  -- Show the sets are equal
  have h_sets_eq : {x | ¬EReal.abs_fun (f - g) x = 0} = {x | ¬f x = g x} := by
    ext x
    simp only [Set.mem_setOf_eq, EReal.abs_fun]
    -- Goal: ¬‖(f - g) x‖.toEReal = 0 ↔ ¬f x = g x
    constructor
    · intro h hfg
      apply h
      simp only [Pi.sub_apply, hfg, sub_self, norm_zero, EReal.coe_zero]
    · intro h heq
      apply h
      have h_norm_zero : ‖(f - g) x‖ = 0 := by
        have : (‖(f - g) x‖ : EReal) = 0 := heq
        exact EReal.coe_eq_zero.mp this
      exact sub_eq_zero.mp (norm_eq_zero.mp h_norm_zero)
  rw [h_sets_eq]

