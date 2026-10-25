import Theorem.Analysis.MeasureTheory.Section_1_3_3.Part2
import Def.Analysis.MeasureTheory.Section_1_3_4


lemma ComplexAbsolutelyIntegrable.abs {d:ℕ} (f: EuclideanSpace' d → ℂ) (hf: ComplexAbsolutelyIntegrable f) : UnsignedAbsolutelyIntegrable (EReal.abs_fun f) := by
  constructor
  · -- UnsignedMeasurable (EReal.abs_fun f)
    constructor
    · -- Unsigned: ∀ x, EReal.abs_fun f x ≥ 0
      intro x
      simp only [EReal.abs_fun]
      exact EReal.coe_nonneg.mpr (norm_nonneg _)
    · -- Exists approximating unsigned simple functions
      obtain ⟨g, hg_simple, hg_conv⟩ := hf.1
      use fun n => EReal.abs_fun (g n)
      constructor
      · intro n; exact (hg_simple n).abs
      · intro x
        simp only [EReal.abs_fun]
        exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)
  · exact hf.2

lemma RealAbsolutelyIntegrable.abs {d:ℕ} (f: EuclideanSpace' d → ℝ) (hf: RealAbsolutelyIntegrable f) : UnsignedAbsolutelyIntegrable (EReal.abs_fun f) := by
  constructor
  · -- UnsignedMeasurable (EReal.abs_fun f)
    constructor
    · intro x
      simp only [EReal.abs_fun]
      exact EReal.coe_nonneg.mpr (norm_nonneg _)
    · obtain ⟨g, hg_simple, hg_conv⟩ := hf.1
      use fun n => EReal.abs_fun (g n)
      constructor
      · intro n; exact (hg_simple n).abs
      · intro x
        simp only [EReal.abs_fun]
        exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)
  · exact hf.2

lemma RealAbsolutelyIntegrable.iff {d:ℕ} (f: EuclideanSpace' d → ℝ) : RealAbsolutelyIntegrable f ↔ ComplexAbsolutelyIntegrable (fun x ↦ (f x:ℂ)) := by
  constructor
  · intro ⟨hf_meas, hf_integ⟩
    constructor
    · exact RealMeasurable.iff.mp hf_meas
    · convert hf_integ using 2
      funext x
      simp only [EReal.abs_fun]
      congr 1
      rw [Complex.norm_real, Real.norm_eq_abs]
  · intro ⟨hf_meas, hf_integ⟩
    constructor
    · exact RealMeasurable.iff.mpr hf_meas
    · convert hf_integ using 2
      funext x
      simp only [EReal.abs_fun]
      congr 1
      rw [Complex.norm_real, Real.norm_eq_abs]

lemma ComplexAbsolutelyIntegrable.re {d:ℕ} (f: EuclideanSpace' d → ℂ) (hf: ComplexAbsolutelyIntegrable f) : RealAbsolutelyIntegrable (Complex.re_fun f) := by
  have h_re_meas : RealMeasurable (Complex.re_fun f) := ComplexMeasurable.iff.mp hf.1 |>.1
  constructor
  · exact h_re_meas
  · have h_le : ∀ x, EReal.abs_fun (Complex.re_fun f) x ≤ EReal.abs_fun f x := fun x => by
      simp only [EReal.abs_fun, Complex.re_fun]
      apply EReal.coe_le_coe_iff.mpr
      rw [Real.norm_eq_abs]
      exact Complex.abs_re_le_norm (f x)
    -- Build UnsignedMeasurable for |Re(f)| directly from RealMeasurable (re_fun f)
    have h_re_abs_meas : UnsignedMeasurable (EReal.abs_fun (Complex.re_fun f)) := by
      constructor
      · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
      · obtain ⟨g, hg_simple, hg_conv⟩ := h_re_meas
        use fun n => EReal.abs_fun (g n)
        constructor
        · intro n; exact (hg_simple n).abs
        · intro x
          simp only [EReal.abs_fun, Complex.re_fun]
          exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)
    have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f)) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun f) := by
      apply LowerUnsignedLebesgueIntegral.mono
      · exact h_re_abs_meas
      · exact hf.abs.1
      · exact AlmostAlways.ofAlways h_le
    exact lt_of_le_of_lt h_mono hf.2

lemma ComplexAbsolutelyIntegrable.im {d:ℕ} (f: EuclideanSpace' d → ℂ) (hf: ComplexAbsolutelyIntegrable f) : RealAbsolutelyIntegrable (Complex.im_fun f) := by
  have h_im_meas : RealMeasurable (Complex.im_fun f) := ComplexMeasurable.iff.mp hf.1 |>.2
  constructor
  · exact h_im_meas
  · have h_le : ∀ x, EReal.abs_fun (Complex.im_fun f) x ≤ EReal.abs_fun f x := fun x => by
      simp only [EReal.abs_fun, Complex.im_fun]
      apply EReal.coe_le_coe_iff.mpr
      rw [Real.norm_eq_abs]
      exact Complex.abs_im_le_norm (f x)
    -- Build UnsignedMeasurable for |Im(f)| directly from RealMeasurable (im_fun f)
    have h_im_abs_meas : UnsignedMeasurable (EReal.abs_fun (Complex.im_fun f)) := by
      constructor
      · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
      · obtain ⟨g, hg_simple, hg_conv⟩ := h_im_meas
        use fun n => EReal.abs_fun (g n)
        constructor
        · intro n; exact (hg_simple n).abs
        · intro x
          simp only [EReal.abs_fun, Complex.im_fun]
          exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)
    have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun f)) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun f) := by
      apply LowerUnsignedLebesgueIntegral.mono
      · exact h_im_abs_meas
      · exact hf.abs.1
      · exact AlmostAlways.ofAlways h_le
    exact lt_of_le_of_lt h_mono hf.2

lemma ComplexAbsolutelyIntegrable.iff {d:ℕ} (f: EuclideanSpace' d → ℂ) : ComplexAbsolutelyIntegrable f ↔ RealAbsolutelyIntegrable (Complex.re_fun f) ∧ RealAbsolutelyIntegrable (Complex.im_fun f) := by
  constructor
  · intro hf
    exact ⟨ComplexAbsolutelyIntegrable.re f hf, ComplexAbsolutelyIntegrable.im f hf⟩
  · intro ⟨hre, him⟩
    constructor
    · exact ComplexMeasurable.iff.mpr ⟨hre.1, him.1⟩
    · -- Use |f| ≤ |Re(f)| + |Im(f)| to bound the integral
      have h_bound : ∀ x, EReal.abs_fun f x ≤
          (EReal.abs_fun (Complex.re_fun f) + EReal.abs_fun (Complex.im_fun f)) x := fun x => by
        simp only [EReal.abs_fun, Complex.re_fun, Complex.im_fun, Pi.add_apply]
        apply EReal.coe_le_coe_iff.mpr
        calc ‖f x‖ = Real.sqrt ((f x).re^2 + (f x).im^2) := Complex.norm_eq_sqrt_sq_add_sq (f x)
          _ ≤ |((f x).re)| + |(f x).im| := by
            have h1 : (f x).re^2 + (f x).im^2 ≤ (|(f x).re| + |(f x).im|)^2 := by
              have h_cross : 0 ≤ 2 * |(f x).re| * |(f x).im| := by positivity
              calc (f x).re^2 + (f x).im^2
                  ≤ (f x).re^2 + 2 * |(f x).re| * |(f x).im| + (f x).im^2 := by linarith
                _ = |(f x).re|^2 + 2 * |(f x).re| * |(f x).im| + |(f x).im|^2 := by rw [sq_abs, sq_abs]
                _ = (|(f x).re| + |(f x).im|)^2 := by ring
            have h2 : 0 ≤ |(f x).re| + |(f x).im| := by positivity
            calc Real.sqrt ((f x).re^2 + (f x).im^2)
                ≤ Real.sqrt ((|(f x).re| + |(f x).im|)^2) := Real.sqrt_le_sqrt h1
              _ = |(f x).re| + |(f x).im| := Real.sqrt_sq h2
          _ = ‖(f x).re‖ + ‖(f x).im‖ := by rw [Real.norm_eq_abs, Real.norm_eq_abs]
      -- Apply monotonicity and additivity of integral
      have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun f) ≤
                    UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f) +
                                              EReal.abs_fun (Complex.im_fun f)) := by
        apply LowerUnsignedLebesgueIntegral.mono
        · constructor
          · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
          · obtain ⟨g, hg_simple, hg_conv⟩ := ComplexMeasurable.iff.mpr ⟨hre.1, him.1⟩
            use fun n => EReal.abs_fun (g n)
            constructor
            · intro n; exact (hg_simple n).abs
            · intro x
              simp only [EReal.abs_fun]
              exact (continuous_coe_real_ereal.comp continuous_norm).continuousAt.tendsto.comp (hg_conv x)
        · exact hre.abs.1.add him.abs.1
        · exact AlmostAlways.ofAlways h_bound
      -- UnsignedLebesgueIntegral is defined as LowerUnsignedLebesgueIntegral
      have h_add : UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f) +
                                             EReal.abs_fun (Complex.im_fun f)) =
                   UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f)) +
                   UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun f)) := by
        exact LowerUnsignedLebesgueIntegral.add hre.abs.1 him.abs.1
          (UnsignedMeasurable.add hre.abs.1 him.abs.1)
      rw [h_add] at h_mono
      calc UnsignedLebesgueIntegral (EReal.abs_fun f)
          ≤ UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f)) +
            UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun f)) := h_mono
        _ < ⊤ := EReal.add_lt_top (lt_top_iff_ne_top.mp hre.2) (lt_top_iff_ne_top.mp him.2)

