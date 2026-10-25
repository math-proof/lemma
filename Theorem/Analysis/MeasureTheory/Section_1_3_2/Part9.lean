import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
import Mathlib.Algebra.Order.Floor.Semifield
import Def.Analysis.MeasureTheory.Section_1_3_2.Part9
set_option doc.verso.suggestions false


theorem RealMeasurable.iff {d:ℕ} {f: EuclideanSpace' d → ℝ} : RealMeasurable f ↔ ComplexMeasurable (Real.complex_fun f) := by
  constructor
  -- Forward: RealMeasurable f → ComplexMeasurable (Real.complex_fun f)
  · intro ⟨g, hg_simple, hg_conv⟩
    use fun n => Real.complex_fun (g n)
    constructor
    · intro n; exact (hg_simple n).toComplex
    · intro x
      simp only [Real.complex_fun]
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp (hg_conv x)
  -- Backward: ComplexMeasurable (Real.complex_fun f) → RealMeasurable f
  · intro ⟨g, hg_simple, hg_conv⟩
    use fun n => Complex.re_fun (g n)
    constructor
    · intro n; exact (hg_simple n).re
    · intro x
      simp only [Complex.re_fun]
      have h := hg_conv x
      simp only [Real.complex_fun] at h
      have h' := Complex.continuous_re.continuousAt.tendsto.comp h
      simp only [Complex.ofReal_re] at h'
      exact h'

theorem ComplexMeasurable.iff {d:ℕ} {f: EuclideanSpace' d → ℂ} : ComplexMeasurable f ↔ RealMeasurable (Complex.re_fun f) ∧ RealMeasurable (Complex.im_fun f) := by
  constructor
  -- Forward: ComplexMeasurable f → RealMeasurable (re ∘ f) ∧ RealMeasurable (im ∘ f)
  · intro ⟨g, hg_simple, hg_conv⟩
    constructor
    · use fun n => Complex.re_fun (g n)
      exact ⟨fun n => (hg_simple n).re, fun x => Complex.continuous_re.continuousAt.tendsto.comp (hg_conv x)⟩
    · use fun n => Complex.im_fun (g n)
      exact ⟨fun n => (hg_simple n).im, fun x => Complex.continuous_im.continuousAt.tendsto.comp (hg_conv x)⟩
  -- Backward: RealMeasurable (re ∘ f) ∧ RealMeasurable (im ∘ f) → ComplexMeasurable f
  · intro ⟨⟨g_re, hg_re_simple, hg_re_conv⟩, ⟨g_im, hg_im_simple, hg_im_conv⟩⟩
    use fun n => Real.complex_fun (g_re n) + Complex.I • Real.complex_fun (g_im n)
    constructor
    · intro n
      exact ((hg_re_simple n).toComplex).add ((hg_im_simple n).toComplex.smul Complex.I)
    · intro x
      have h_re := hg_re_conv x; simp only [Complex.re_fun] at h_re
      have h_im := hg_im_conv x; simp only [Complex.im_fun] at h_im
      have h_re' := Complex.continuous_ofReal.continuousAt.tendsto.comp h_re
      have h_im' := Complex.continuous_ofReal.continuousAt.tendsto.comp h_im
      have h_sum : Filter.Tendsto (fun n => Complex.ofReal (g_re n x) + Complex.I * Complex.ofReal (g_im n x))
          Filter.atTop (nhds (Complex.ofReal (f x).re + Complex.I * Complex.ofReal (f x).im)) :=
        h_re'.add (h_im'.const_mul Complex.I)
      have h_eq : Complex.ofReal (f x).re + Complex.I * Complex.ofReal (f x).im =
                  Complex.ofReal (f x).re + Complex.ofReal (f x).im * Complex.I := by ring
      rw [h_eq, Complex.re_add_im] at h_sum
      simp only [Pi.add_apply, Pi.smul_apply, Real.complex_fun, smul_eq_mul]
      exact h_sum

/-- Exercise 1.3.8(i) -/
theorem Continuous.RealMeasurable {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: Continuous f) : RealMeasurable f := by
  have h_iff : _root_.RealMeasurable f ↔ ∀ U, IsOpen U → LebesgueMeasurable (f ⁻¹' U) :=
    (_root_.RealMeasurable.TFAE (f := f)).out 1 4
  exact h_iff.mpr fun U hU => IsOpen.measurable (hU.preimage hf)

theorem Continuous.ComplexMeasurable {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: Continuous f) : ComplexMeasurable f := by
  have h_iff : _root_.ComplexMeasurable f ↔ ∀ U, IsOpen U → LebesgueMeasurable (f ⁻¹' U) :=
    (_root_.ComplexMeasurable.TFAE (f := f)).out 1 5
  exact h_iff.mpr fun U hU => IsOpen.measurable (hU.preimage hf)

/-- Exercise 1.3.8(iii) -/
theorem RealMeasurable.aeEqual {d:ℕ} {f g: EuclideanSpace' d → ℝ} (hf: RealMeasurable f)
    (heq: AlmostEverywhereEqual f g) : RealMeasurable g := by
  obtain ⟨u, hu, huf⟩ := hf
  have h_iff : RealMeasurable g ↔ ∃ u, (∀ n, RealSimpleFunction (u n)) ∧
      PointwiseAeConvergesTo u g := (RealMeasurable.TFAE (f := g)).out 1 2
  refine h_iff.mpr ⟨u, hu, ?_⟩
  exact AlmostAlways.mp heq fun x hx => hx ▸ huf x

theorem ComplexMeasurable.aeEqual {d:ℕ} {f g: EuclideanSpace' d → ℂ} (hf: ComplexMeasurable f)
    (heq: AlmostEverywhereEqual f g) : ComplexMeasurable g := by
  obtain ⟨u, hu, huf⟩ := hf
  have h_iff : ComplexMeasurable g ↔ ∃ u, (∀ n, ComplexSimpleFunction (u n)) ∧
      PointwiseAeConvergesTo u g := (ComplexMeasurable.TFAE (f := g)).out 1 2
  refine h_iff.mpr ⟨u, hu, ?_⟩
  exact AlmostAlways.mp heq fun x hx => hx ▸ huf x

/-- Exercise 1.3.8(v) -/
theorem RealMeasurable.comp_cts {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealMeasurable f) {φ: ℝ → ℝ} (hφ: Continuous φ)  : RealMeasurable (φ ∘ f) := by
  have h_source : RealMeasurable f ↔ ∀ U, IsOpen U → LebesgueMeasurable (f ⁻¹' U) :=
    (RealMeasurable.TFAE (f := f)).out 1 4
  have h_target : RealMeasurable (φ ∘ f) ↔ ∀ U, IsOpen U → LebesgueMeasurable ((φ ∘ f) ⁻¹' U) :=
    (RealMeasurable.TFAE (f := φ ∘ f)).out 1 4
  exact h_target.mpr fun U hU => h_source.mp hf (φ ⁻¹' U) (hU.preimage hφ)

theorem ComplexMeasurable.comp_cts {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexMeasurable f) {φ: ℂ → ℂ} (hφ: Continuous φ)  : ComplexMeasurable (φ ∘ f) := by
  have h_source : ComplexMeasurable f ↔ ∀ U, IsOpen U → LebesgueMeasurable (f ⁻¹' U) :=
    (ComplexMeasurable.TFAE (f := f)).out 1 5
  have h_target : ComplexMeasurable (φ ∘ f) ↔ ∀ U, IsOpen U → LebesgueMeasurable ((φ ∘ f) ⁻¹' U) :=
    (ComplexMeasurable.TFAE (f := φ ∘ f)).out 1 5
  exact h_target.mpr fun U hU => h_source.mp hf (φ ⁻¹' U) (hU.preimage hφ)

/-- Exercise 1.3.8(vi) (Sum of measurable functions) -/
theorem RealMeasurable.add {d:ℕ} {f g: EuclideanSpace' d → ℝ} (hf: RealMeasurable f) (hg: RealMeasurable g) : RealMeasurable (f + g) := by
  obtain ⟨u, hu, huf⟩ := hf
  obtain ⟨v, hv, hvg⟩ := hg
  refine ⟨fun n => u n + v n, fun n => (hu n).add (hv n), ?_⟩
  intro x
  exact (huf x).add (hvg x)

theorem ComplexMeasurable.add {d:ℕ} {f g: EuclideanSpace' d → ℂ} (hf: ComplexMeasurable f) (hg: ComplexMeasurable g) : ComplexMeasurable (f + g) := by
  obtain ⟨u, hu, huf⟩ := hf
  obtain ⟨v, hv, hvg⟩ := hg
  refine ⟨fun n => u n + v n, fun n => (hu n).add (hv n), ?_⟩
  intro x
  exact (huf x).add (hvg x)

/-- Exercise 1.3.8(vi') (Difference of measurable functions) -/
theorem RealMeasurable.sub {d:ℕ} {f g: EuclideanSpace' d → ℝ} (hf: RealMeasurable f) (hg: RealMeasurable g) : RealMeasurable (f - g) := by
  obtain ⟨u, hu, huf⟩ := hf
  obtain ⟨v, hv, hvg⟩ := hg
  refine ⟨fun n => u n + (-1 : ℝ) • v n, fun n => (hu n).add ((hv n).smul (-1)), ?_⟩
  intro x
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_one_mul, sub_eq_add_neg,
    Pi.sub_apply] using (huf x).sub (hvg x)

theorem ComplexMeasurable.sub {d:ℕ} {f g: EuclideanSpace' d → ℂ} (hf: ComplexMeasurable f) (hg: ComplexMeasurable g) : ComplexMeasurable (f - g) := by
  obtain ⟨u, hu, huf⟩ := hf
  obtain ⟨v, hv, hvg⟩ := hg
  refine ⟨fun n => u n + (-1 : ℂ) • v n, fun n => (hu n).add ((hv n).smul (-1)), ?_⟩
  intro x
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_one_mul, sub_eq_add_neg,
    Pi.sub_apply] using (huf x).sub (hvg x)

