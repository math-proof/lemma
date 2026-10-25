import Theorem.Analysis.MeasureTheory.Section_1_3_3.Part2
import Def.Analysis.MeasureTheory.Section_1_3_4.Part2


theorem RealAbsolutelyIntegrable.add {d:ℕ} {f g: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) (hg: RealAbsolutelyIntegrable g) : RealAbsolutelyIntegrable (f + g) := by
  constructor
  · exact RealMeasurable.add hf.1 hg.1
  · -- Show ∫ |f + g| ≤ ∫ |f| + ∫ |g| < ∞
    have h_le : ∀ x, EReal.abs_fun (f + g) x ≤ (EReal.abs_fun f + EReal.abs_fun g) x := fun x => by
      simp only [EReal.abs_fun, Pi.add_apply]
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (norm_add_le (f x) (g x))
    have hf_abs := RealAbsolutelyIntegrable.abs f hf
    have hg_abs := RealAbsolutelyIntegrable.abs g hg
    have hfg_abs_meas : UnsignedMeasurable (EReal.abs_fun (f + g)) := by
      constructor
      · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
      · obtain ⟨gf, hgf_simple, hgf_conv⟩ := hf.1
        obtain ⟨gg, hgg_simple, hgg_conv⟩ := hg.1
        use fun n => EReal.abs_fun (gf n + gg n)
        constructor
        · intro n; exact (RealSimpleFunction.add (hgf_simple n) (hgg_simple n)).abs
        · intro x
          simp only [EReal.abs_fun]
          have hcont : Continuous (fun y : ℝ => ‖y‖.toEReal) :=
            continuous_coe_real_ereal.comp continuous_norm
          have hconv : Filter.Tendsto (fun n => gf n x + gg n x) Filter.atTop (nhds (f x + g x)) :=
            Filter.Tendsto.add (hgf_conv x) (hgg_conv x)
          exact hcont.continuousAt.tendsto.comp hconv
    have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f + g)) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun f + EReal.abs_fun g) := by
      apply LowerUnsignedLebesgueIntegral.mono hfg_abs_meas (UnsignedMeasurable.add hf_abs.1 hg_abs.1)
      exact AlmostAlways.ofAlways h_le
    have h_add : UnsignedLebesgueIntegral (EReal.abs_fun f + EReal.abs_fun g) =
                 UnsignedLebesgueIntegral (EReal.abs_fun f) + UnsignedLebesgueIntegral (EReal.abs_fun g) := by
      apply LowerUnsignedLebesgueIntegral.add hf_abs.1 hg_abs.1 (UnsignedMeasurable.add hf_abs.1 hg_abs.1)
    calc UnsignedLebesgueIntegral (EReal.abs_fun (f + g))
        ≤ UnsignedLebesgueIntegral (EReal.abs_fun f) + UnsignedLebesgueIntegral (EReal.abs_fun g) := by
          rw [← h_add]; exact h_mono
      _ < ⊤ := EReal.add_lt_top hf.2.ne_top hg.2.ne_top

theorem ComplexAbsolutelyIntegrable.add {d:ℕ} {f g: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) (hg: ComplexAbsolutelyIntegrable g) : ComplexAbsolutelyIntegrable (f + g) := by
  constructor
  · exact ComplexMeasurable.add hf.1 hg.1
  · have h_le : ∀ x, EReal.abs_fun (f + g) x ≤ (EReal.abs_fun f + EReal.abs_fun g) x := fun x => by
      simp only [EReal.abs_fun, Pi.add_apply]
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (norm_add_le (f x) (g x))
    have hf_abs := ComplexAbsolutelyIntegrable.abs f hf
    have hg_abs := ComplexAbsolutelyIntegrable.abs g hg
    have hfg_abs_meas : UnsignedMeasurable (EReal.abs_fun (f + g)) := by
      constructor
      · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
      · obtain ⟨gf, hgf_simple, hgf_conv⟩ := hf.1
        obtain ⟨gg, hgg_simple, hgg_conv⟩ := hg.1
        use fun n => EReal.abs_fun (gf n + gg n)
        constructor
        · intro n; exact (ComplexSimpleFunction.add (hgf_simple n) (hgg_simple n)).abs
        · intro x
          simp only [EReal.abs_fun]
          have hcont : Continuous (fun y : ℂ => ‖y‖.toEReal) :=
            continuous_coe_real_ereal.comp continuous_norm
          have hconv : Filter.Tendsto (fun n => gf n x + gg n x) Filter.atTop (nhds (f x + g x)) :=
            Filter.Tendsto.add (hgf_conv x) (hgg_conv x)
          exact hcont.continuousAt.tendsto.comp hconv
    have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f + g)) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun f + EReal.abs_fun g) := by
      apply LowerUnsignedLebesgueIntegral.mono hfg_abs_meas (UnsignedMeasurable.add hf_abs.1 hg_abs.1)
      exact AlmostAlways.ofAlways h_le
    have h_add : UnsignedLebesgueIntegral (EReal.abs_fun f + EReal.abs_fun g) =
                 UnsignedLebesgueIntegral (EReal.abs_fun f) + UnsignedLebesgueIntegral (EReal.abs_fun g) := by
      apply LowerUnsignedLebesgueIntegral.add hf_abs.1 hg_abs.1 (UnsignedMeasurable.add hf_abs.1 hg_abs.1)
    calc UnsignedLebesgueIntegral (EReal.abs_fun (f + g))
        ≤ UnsignedLebesgueIntegral (EReal.abs_fun f) + UnsignedLebesgueIntegral (EReal.abs_fun g) := by
          rw [← h_add]; exact h_mono
      _ < ⊤ := EReal.add_lt_top hf.2.ne_top hg.2.ne_top

theorem RealAbsolutelyIntegrable.sub {d:ℕ} {f g: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) (hg: RealAbsolutelyIntegrable g) : RealAbsolutelyIntegrable (f - g) := by
  constructor
  · exact RealMeasurable.sub hf.1 hg.1
  · have h_le : ∀ x, EReal.abs_fun (f - g) x ≤ (EReal.abs_fun f + EReal.abs_fun g) x := fun x => by
      simp only [EReal.abs_fun, Pi.sub_apply, Pi.add_apply]
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (norm_sub_le (f x) (g x))
    have hf_abs := RealAbsolutelyIntegrable.abs f hf
    have hg_abs := RealAbsolutelyIntegrable.abs g hg
    have hfg_abs_meas : UnsignedMeasurable (EReal.abs_fun (f - g)) := by
      constructor
      · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
      · obtain ⟨gf, hgf_simple, hgf_conv⟩ := hf.1
        obtain ⟨gg, hgg_simple, hgg_conv⟩ := hg.1
        use fun n => EReal.abs_fun (gf n - gg n)
        constructor
        · intro n
          have hsub : RealSimpleFunction (gf n - gg n) := by
            have heq : gf n - gg n = gf n + (-1 : ℝ) • gg n := by
              funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
            rw [heq]
            exact RealSimpleFunction.add (hgf_simple n) ((hgg_simple n).smul (-1))
          exact hsub.abs
        · intro x
          simp only [EReal.abs_fun]
          have hcont : Continuous (fun y : ℝ => ‖y‖.toEReal) :=
            continuous_coe_real_ereal.comp continuous_norm
          have hconv : Filter.Tendsto (fun n => gf n x - gg n x) Filter.atTop (nhds (f x - g x)) :=
            Filter.Tendsto.sub (hgf_conv x) (hgg_conv x)
          exact hcont.continuousAt.tendsto.comp hconv
    have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun f + EReal.abs_fun g) := by
      apply LowerUnsignedLebesgueIntegral.mono hfg_abs_meas (UnsignedMeasurable.add hf_abs.1 hg_abs.1)
      exact AlmostAlways.ofAlways h_le
    have h_add : UnsignedLebesgueIntegral (EReal.abs_fun f + EReal.abs_fun g) =
                 UnsignedLebesgueIntegral (EReal.abs_fun f) + UnsignedLebesgueIntegral (EReal.abs_fun g) := by
      apply LowerUnsignedLebesgueIntegral.add hf_abs.1 hg_abs.1 (UnsignedMeasurable.add hf_abs.1 hg_abs.1)
    calc UnsignedLebesgueIntegral (EReal.abs_fun (f - g))
        ≤ UnsignedLebesgueIntegral (EReal.abs_fun f) + UnsignedLebesgueIntegral (EReal.abs_fun g) := by
          rw [← h_add]; exact h_mono
      _ < ⊤ := EReal.add_lt_top hf.2.ne_top hg.2.ne_top

theorem ComplexAbsolutelyIntegrable.sub {d:ℕ} {f g: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) (hg: ComplexAbsolutelyIntegrable g) : ComplexAbsolutelyIntegrable (f - g) := by
  constructor
  · exact ComplexMeasurable.sub hf.1 hg.1
  · have h_le : ∀ x, EReal.abs_fun (f - g) x ≤ (EReal.abs_fun f + EReal.abs_fun g) x := fun x => by
      simp only [EReal.abs_fun, Pi.sub_apply, Pi.add_apply]
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (norm_sub_le (f x) (g x))
    have hf_abs := ComplexAbsolutelyIntegrable.abs f hf
    have hg_abs := ComplexAbsolutelyIntegrable.abs g hg
    have hfg_abs_meas : UnsignedMeasurable (EReal.abs_fun (f - g)) := by
      constructor
      · intro x; simp only [EReal.abs_fun]; exact EReal.coe_nonneg.mpr (norm_nonneg _)
      · obtain ⟨gf, hgf_simple, hgf_conv⟩ := hf.1
        obtain ⟨gg, hgg_simple, hgg_conv⟩ := hg.1
        use fun n => EReal.abs_fun (gf n - gg n)
        constructor
        · intro n
          have hsub : ComplexSimpleFunction (gf n - gg n) := by
            have heq : gf n - gg n = gf n + (-1 : ℂ) • gg n := by
              funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
            rw [heq]
            exact ComplexSimpleFunction.add (hgf_simple n) ((hgg_simple n).smul (-1))
          exact hsub.abs
        · intro x
          simp only [EReal.abs_fun]
          have hcont : Continuous (fun y : ℂ => ‖y‖.toEReal) :=
            continuous_coe_real_ereal.comp continuous_norm
          have hconv : Filter.Tendsto (fun n => gf n x - gg n x) Filter.atTop (nhds (f x - g x)) :=
            Filter.Tendsto.sub (hgf_conv x) (hgg_conv x)
          exact hcont.continuousAt.tendsto.comp hconv
    have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≤
                  UnsignedLebesgueIntegral (EReal.abs_fun f + EReal.abs_fun g) := by
      apply LowerUnsignedLebesgueIntegral.mono hfg_abs_meas (UnsignedMeasurable.add hf_abs.1 hg_abs.1)
      exact AlmostAlways.ofAlways h_le
    have h_add : UnsignedLebesgueIntegral (EReal.abs_fun f + EReal.abs_fun g) =
                 UnsignedLebesgueIntegral (EReal.abs_fun f) + UnsignedLebesgueIntegral (EReal.abs_fun g) := by
      apply LowerUnsignedLebesgueIntegral.add hf_abs.1 hg_abs.1 (UnsignedMeasurable.add hf_abs.1 hg_abs.1)
    calc UnsignedLebesgueIntegral (EReal.abs_fun (f - g))
        ≤ UnsignedLebesgueIntegral (EReal.abs_fun f) + UnsignedLebesgueIntegral (EReal.abs_fun g) := by
          rw [← h_add]; exact h_mono
      _ < ⊤ := EReal.add_lt_top hf.2.ne_top hg.2.ne_top

theorem RealAbsolutelyIntegrable.smul {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) (c:ℝ) : RealAbsolutelyIntegrable (c • f) := by
  constructor
  · -- RealMeasurable (c • f)
    obtain ⟨g, hg_simple, hg_conv⟩ := hf.1
    use fun n => c • g n
    constructor
    · intro n; exact (hg_simple n).smul c
    · intro x
      have hconv : Filter.Tendsto (fun n => g n x) Filter.atTop (nhds (f x)) := hg_conv x
      have hsmul_conv : Filter.Tendsto (fun n => c • g n x) Filter.atTop (nhds (c • f x)) := by
        simp only [smul_eq_mul]
        exact hconv.const_mul c
      simp only [Pi.smul_apply]
      exact hsmul_conv
  · -- UnsignedLebesgueIntegral (EReal.abs_fun (c • f)) < ⊤
    have h_eq : ∀ x, EReal.abs_fun (c • f) x = ‖c‖.toEReal * EReal.abs_fun f x := fun x => by
      simp only [EReal.abs_fun, Pi.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs]
      rw [EReal.coe_mul]
    have hf_abs := RealAbsolutelyIntegrable.abs f hf
    have h_smul_eq : EReal.abs_fun (c • f) = (fun x => ‖c‖.toEReal * EReal.abs_fun f x) := by
      funext x; exact h_eq x
    rw [h_smul_eq]
    have h_scale : UnsignedLebesgueIntegral (fun x => ‖c‖.toEReal * EReal.abs_fun f x) =
                   ‖c‖.toEReal * UnsignedLebesgueIntegral (EReal.abs_fun f) := by
      have h_eq' : (fun x => ‖c‖.toEReal * EReal.abs_fun f x) = (‖c‖.toEReal : EReal) • EReal.abs_fun f := by
        funext x; simp only [Pi.smul_apply, smul_eq_mul]
      rw [h_eq', UnsignedLebesgueIntegral]
      have h_hom := LowerUnsignedLebesgueIntegral.hom hf_abs.1 (norm_nonneg c)
      exact h_hom
    rw [h_scale]
    by_cases hc : c = 0
    · simp only [hc, norm_zero]
      rw [show (0 : ℝ).toEReal = 0 by rfl, zero_mul]
      exact EReal.coe_lt_top 0
    · have hc_pos : ‖c‖ > 0 := norm_pos_iff.mpr hc
      have h_ne_top : ‖c‖.toEReal * UnsignedLebesgueIntegral (EReal.abs_fun f) ≠ ⊤ := by
        rw [EReal.mul_ne_top]
        refine ⟨?_, ?_, ?_, ?_⟩
        · left; exact EReal.coe_ne_bot ‖c‖
        · left; exact le_of_lt (EReal.coe_pos.mpr hc_pos)
        · left; exact EReal.coe_ne_top ‖c‖
        · right; exact hf.2.ne_top
      exact Ne.lt_top h_ne_top

theorem ComplexAbsolutelyIntegrable.smul {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) (c:ℂ) : ComplexAbsolutelyIntegrable (c • f) := by
  constructor
  · -- ComplexMeasurable (c • f)
    obtain ⟨g, hg_simple, hg_conv⟩ := hf.1
    use fun n => c • g n
    constructor
    · intro n; exact (hg_simple n).smul c
    · intro x
      have hconv : Filter.Tendsto (fun n => g n x) Filter.atTop (nhds (f x)) := hg_conv x
      have hsmul_conv : Filter.Tendsto (fun n => c • g n x) Filter.atTop (nhds (c • f x)) := by
        simp only [smul_eq_mul]
        exact hconv.const_mul c
      simp only [Pi.smul_apply]
      exact hsmul_conv
  · -- UnsignedLebesgueIntegral (EReal.abs_fun (c • f)) < ⊤
    have h_eq : ∀ x, EReal.abs_fun (c • f) x = ‖c‖.toEReal * EReal.abs_fun f x := fun x => by
      simp only [EReal.abs_fun, Pi.smul_apply, smul_eq_mul, norm_mul]
      rw [EReal.coe_mul]
    have hf_abs := ComplexAbsolutelyIntegrable.abs f hf
    have h_smul_eq : EReal.abs_fun (c • f) = (fun x => ‖c‖.toEReal * EReal.abs_fun f x) := by
      funext x; exact h_eq x
    rw [h_smul_eq]
    have h_scale : UnsignedLebesgueIntegral (fun x => ‖c‖.toEReal * EReal.abs_fun f x) =
                   ‖c‖.toEReal * UnsignedLebesgueIntegral (EReal.abs_fun f) := by
      have h_eq' : (fun x => ‖c‖.toEReal * EReal.abs_fun f x) = (‖c‖.toEReal : EReal) • EReal.abs_fun f := by
        funext x; simp only [Pi.smul_apply, smul_eq_mul]
      rw [h_eq', UnsignedLebesgueIntegral]
      have h_hom := LowerUnsignedLebesgueIntegral.hom hf_abs.1 (norm_nonneg c)
      exact h_hom
    rw [h_scale]
    by_cases hc : c = 0
    · simp only [hc, norm_zero]
      rw [show (0 : ℝ).toEReal = 0 by rfl, zero_mul]
      exact EReal.coe_lt_top 0
    · have hc_pos : ‖c‖ > 0 := norm_pos_iff.mpr hc
      have h_ne_top : ‖c‖.toEReal * UnsignedLebesgueIntegral (EReal.abs_fun f) ≠ ⊤ := by
        rw [EReal.mul_ne_top]
        refine ⟨?_, ?_, ?_, ?_⟩
        · left; exact EReal.coe_ne_bot ‖c‖
        · left; exact le_of_lt (EReal.coe_pos.mpr hc_pos)
        · left; exact EReal.coe_ne_top ‖c‖
        · right; exact hf.2.ne_top
      exact Ne.lt_top h_ne_top

theorem RealAbsolutelyIntegrable.of_neg {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) : RealAbsolutelyIntegrable (-f) := by
  have h : -f = (-1 : ℝ) • f := by funext x; simp [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  rw [h]
  exact hf.smul (-1)

theorem ComplexAbsolutelyIntegrable.of_neg {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) : ComplexAbsolutelyIntegrable (-f) := by
  have h : -f = (-1 : ℂ) • f := by funext x; simp [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  rw [h]
  exact hf.smul (-1)

theorem ComplexAbsolutelyIntegrable.conj {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) : ComplexAbsolutelyIntegrable (Complex.conj_fun f) := by
  constructor
  · -- ComplexMeasurable (Complex.conj_fun f)
    obtain ⟨g, hg_simple, hg_conv⟩ := hf.1
    use fun n => Complex.conj_fun (g n)
    constructor
    · intro n; exact (hg_simple n).conj
    · intro x
      simp only [Complex.conj_fun]
      have hconv : Filter.Tendsto (fun n => g n x) Filter.atTop (nhds (f x)) := hg_conv x
      exact (RCLike.continuous_conj.tendsto (f x)).comp hconv
  · -- UnsignedLebesgueIntegral (EReal.abs_fun (Complex.conj_fun f)) < ⊤
    have h_eq : EReal.abs_fun (Complex.conj_fun f) = EReal.abs_fun f := by
      funext x
      simp only [EReal.abs_fun, Complex.conj_fun, RCLike.norm_conj]
    rw [h_eq]
    exact hf.2

