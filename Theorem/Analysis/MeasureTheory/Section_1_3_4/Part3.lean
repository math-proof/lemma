import Theorem.Analysis.MeasureTheory.Section_1_3_3.Part2
import Def.Analysis.MeasureTheory.Section_1_3_4.Part3


lemma ComplexAbsolutelyIntegrable.zero {d:ℕ} : ComplexAbsolutelyIntegrable (0 : EuclideanSpace' d → ℂ) := by
  constructor
  · -- ComplexMeasurable 0
    use fun _ => 0
    constructor
    · intro n
      use 0, fun _ => 0, fun _ => ∅
      constructor
      · intro i; exact Fin.elim0 i
      · funext x; simp only [Pi.zero_apply, Finset.univ_eq_empty, Finset.sum_empty]
    · intro x; exact tendsto_const_nhds
  · -- UnsignedLebesgueIntegral (EReal.abs_fun 0) < ⊤
    have h_zero : EReal.abs_fun (0 : EuclideanSpace' d → ℂ) = 0 := by
      funext x; simp only [EReal.abs_fun, Pi.zero_apply, norm_zero]; rfl
    rw [h_zero, UnsignedLebesgueIntegral]
    -- Show that 0 is an unsigned simple function
    have h_simple : UnsignedSimpleFunction (0 : EuclideanSpace' d → EReal) := by
      use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
      constructor
      · intro i; exact Fin.elim0 i
      · funext x; simp only [Pi.zero_apply, Finset.univ_eq_empty, Finset.sum_empty]
    rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral h_simple]
    -- The integral of the zero simple function is < ⊤
    -- Key: h_simple.integ ≤ ∑ i, c_i * measure(E_i) where c_i are bounded
    -- For the zero function, each term in any representation contributes 0
    simp only [UnsignedSimpleFunction.integ]
    -- The sum is over Fin (choose ...) which is some natural number
    -- Show it's < ⊤ by showing sum ≤ some finite bound
    apply lt_of_le_of_lt _ (EReal.coe_lt_top (0:ℝ))
    rw [EReal.coe_zero]
    have hcond := h_simple.choose_spec.choose_spec.choose_spec.1
    have hf_eq := h_simple.choose_spec.choose_spec.choose_spec.2
    apply Finset.sum_nonpos
    intro i _
    by_cases hci : h_simple.choose_spec.choose i = 0
    · rw [hci, zero_mul]
    · -- c i > 0, need to show E i is empty
      have hci_pos : h_simple.choose_spec.choose i > 0 := lt_of_le_of_ne (hcond i).2 (Ne.symm hci)
      have hE_empty : h_simple.choose_spec.choose_spec.choose i = ∅ := by
        by_contra hne
        have hne' := Set.nonempty_iff_ne_empty.mpr hne
        obtain ⟨x, hx⟩ := hne'
        have h1 : (0 : EuclideanSpace' d → EReal) x = 0 := rfl
        rw [hf_eq] at h1
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
        have h_nonneg : ∀ j, h_simple.choose_spec.choose j * EReal.indicator (h_simple.choose_spec.choose_spec.choose j) x ≥ 0 := fun j => by
          apply mul_nonneg (hcond j).2
          by_cases hjx : x ∈ h_simple.choose_spec.choose_spec.choose j
          · simp [EReal.indicator_of_mem hjx]
          · simp [EReal.indicator_of_notMem hjx]
        have h_all_zero : ∀ j ∈ Finset.univ, h_simple.choose_spec.choose j * EReal.indicator (h_simple.choose_spec.choose_spec.choose j) x = 0 :=
          Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h_nonneg j) |>.mp h1
        have h_term_i_zero := h_all_zero i (Finset.mem_univ i)
        simp only [EReal.indicator_of_mem hx, mul_one] at h_term_i_zero
        exact (ne_of_gt hci_pos) h_term_i_zero
      rw [hE_empty, Lebesgue_measure.empty, mul_zero]

-- Helper lemma: the norm of zero is zero
lemma ComplexAbsolutelyIntegrable.norm_zero {d:ℕ} : (ComplexAbsolutelyIntegrable.zero (d:=d)).norm = 0 := by
  simp only [ComplexAbsolutelyIntegrable.norm, UnsignedAbsolutelyIntegrable.integ]
  have h_abs_zero : EReal.abs_fun (0 : EuclideanSpace' d → ℂ) = 0 := by
    funext x; simp only [EReal.abs_fun, Pi.zero_apply]; norm_cast
  have h_simple : UnsignedSimpleFunction (0 : EuclideanSpace' d → EReal) := by
    use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
    constructor
    · intro i; exact Fin.elim0 i
    · funext x; simp only [Pi.zero_apply, Finset.univ_eq_empty, Finset.sum_empty]
  calc (UnsignedLebesgueIntegral (EReal.abs_fun 0)).toReal
      = (LowerUnsignedLebesgueIntegral (EReal.abs_fun 0)).toReal := rfl
    _ = (LowerUnsignedLebesgueIntegral 0).toReal := by rw [h_abs_zero]
    _ = h_simple.integ.toReal := by rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral h_simple]
    _ = 0 := by
        -- h_simple.integ is a sum over Fin (h_simple.choose) = Fin k for some k
        -- For the zero function, each term is 0
        simp only [UnsignedSimpleFunction.integ]
        have hcond := h_simple.choose_spec.choose_spec.choose_spec.1
        have hf_eq := h_simple.choose_spec.choose_spec.choose_spec.2
        have h_sum_zero : ∑ i, h_simple.choose_spec.choose i * Lebesgue_measure (h_simple.choose_spec.choose_spec.choose i) = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          by_cases hci : h_simple.choose_spec.choose i = 0
          · rw [hci, zero_mul]
          · have hci_pos : h_simple.choose_spec.choose i > 0 := lt_of_le_of_ne (hcond i).2 (Ne.symm hci)
            have hE_empty : h_simple.choose_spec.choose_spec.choose i = ∅ := by
              by_contra hne
              have hne' := Set.nonempty_iff_ne_empty.mpr hne
              obtain ⟨x, hx⟩ := hne'
              have h1 : (0 : EuclideanSpace' d → EReal) x = 0 := rfl
              rw [hf_eq] at h1
              simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
              have h_nonneg : ∀ j, h_simple.choose_spec.choose j * EReal.indicator (h_simple.choose_spec.choose_spec.choose j) x ≥ 0 := fun j => by
                apply mul_nonneg (hcond j).2
                simp only [EReal.indicator, Real.EReal_fun]
                exact EReal.coe_nonneg.mpr (Set.indicator_nonneg (fun _ _ => zero_le_one) x)
              have h_all_zero : ∀ j ∈ Finset.univ, h_simple.choose_spec.choose j * EReal.indicator (h_simple.choose_spec.choose_spec.choose j) x = 0 :=
                Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h_nonneg j) |>.mp h1
              have h_term_i_zero := h_all_zero i (Finset.mem_univ i)
              simp only [EReal.indicator_of_mem hx, mul_one] at h_term_i_zero
              exact (ne_of_gt hci_pos) h_term_i_zero
            rw [hE_empty, Lebesgue_measure.empty, mul_zero]
        simp only [h_sum_zero, EReal.toReal_zero]

