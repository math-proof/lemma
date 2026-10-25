import Theorem.Analysis.MeasureTheory.Section_1_3_3.Part2
import Theorem.Analysis.MeasureTheory.Section_1_3_4


noncomputable def UnsignedAbsolutelyIntegrable.integ {d:ℕ} (f: EuclideanSpace' d → EReal) (_: UnsignedAbsolutelyIntegrable f) : ℝ := (UnsignedLebesgueIntegral f).toReal

noncomputable def ComplexAbsolutelyIntegrable.norm {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) : ℝ := hf.abs.integ

noncomputable def RealAbsolutelyIntegrable.norm {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) : ℝ := hf.abs.integ

def RealMeasurable.measurable_pos {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealMeasurable f) : UnsignedMeasurable (EReal.pos_fun f) := by
  constructor
  · -- Unsigned: ∀ x, EReal.pos_fun f x ≥ 0
    intro x
    simp only [EReal.pos_fun]
    exact EReal.coe_nonneg.mpr (le_max_right _ _)
  · -- Exists approximating unsigned simple functions
    obtain ⟨g, hg_simple, hg_conv⟩ := hf
    use fun n => EReal.pos_fun (g n)
    constructor
    · intro n; exact (hg_simple n).pos
    · intro x
      simp only [EReal.pos_fun]
      have hcont : Continuous (fun y : ℝ => (max y 0).toEReal) :=
        continuous_coe_real_ereal.comp (continuous_max.comp (continuous_id.prodMk continuous_const))
      exact hcont.continuousAt.tendsto.comp (hg_conv x)

def RealMeasurable.measurable_neg {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealMeasurable f) : UnsignedMeasurable (EReal.neg_fun f) := by
  constructor
  · -- Unsigned: ∀ x, EReal.neg_fun f x ≥ 0
    intro x
    simp only [EReal.neg_fun]
    exact EReal.coe_nonneg.mpr (le_max_right _ _)
  · -- Exists approximating unsigned simple functions
    obtain ⟨g, hg_simple, hg_conv⟩ := hf
    use fun n => EReal.neg_fun (g n)
    constructor
    · intro n; exact (hg_simple n).neg
    · intro x
      simp only [EReal.neg_fun]
      have hcont : Continuous (fun y : ℝ => (max (-y) 0).toEReal) :=
        continuous_coe_real_ereal.comp (continuous_max.comp (continuous_neg.prodMk continuous_const))
      exact hcont.continuousAt.tendsto.comp (hg_conv x)

def RealAbsolutelyIntegrable.pos {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) : UnsignedAbsolutelyIntegrable (EReal.pos_fun f) := by
  constructor
  · exact hf.1.measurable_pos
  · -- UnsignedLebesgueIntegral (pos_fun f) ≤ UnsignedLebesgueIntegral (abs_fun f) < ⊤
    have h_le : ∀ x, EReal.pos_fun f x ≤ EReal.abs_fun f x := fun x => by
      simp only [EReal.pos_fun, EReal.abs_fun]
      apply EReal.coe_le_coe_iff.mpr
      rw [Real.norm_eq_abs, max_le_iff]
      exact ⟨le_abs_self _, abs_nonneg _⟩
    have h_mono : UnsignedLebesgueIntegral (EReal.pos_fun f) ≤ UnsignedLebesgueIntegral (EReal.abs_fun f) := by
      apply LowerUnsignedLebesgueIntegral.mono
      · exact hf.1.measurable_pos
      · exact hf.abs.1
      · exact AlmostAlways.ofAlways h_le
    exact lt_of_le_of_lt h_mono hf.2

def RealAbsolutelyIntegrable.neg {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) : UnsignedAbsolutelyIntegrable (EReal.neg_fun f) := by
  constructor
  · exact hf.1.measurable_neg
  · -- UnsignedLebesgueIntegral (neg_fun f) ≤ UnsignedLebesgueIntegral (abs_fun f) < ⊤
    have h_le : ∀ x, EReal.neg_fun f x ≤ EReal.abs_fun f x := fun x => by
      simp only [EReal.neg_fun, EReal.abs_fun]
      apply EReal.coe_le_coe_iff.mpr
      rw [Real.norm_eq_abs, max_le_iff]
      exact ⟨neg_le_abs _, abs_nonneg _⟩
    have h_mono : UnsignedLebesgueIntegral (EReal.neg_fun f) ≤ UnsignedLebesgueIntegral (EReal.abs_fun f) := by
      apply LowerUnsignedLebesgueIntegral.mono
      · exact hf.1.measurable_neg
      · exact hf.abs.1
      · exact AlmostAlways.ofAlways h_le
    exact lt_of_le_of_lt h_mono hf.2

noncomputable def RealAbsolutelyIntegrable.integ {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealAbsolutelyIntegrable f) : ℝ := hf.pos.integ - hf.neg.integ

noncomputable def ComplexAbsolutelyIntegrable.integ {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) : ℂ := hf.re.integ + Complex.I * hf.im.integ

open Classical in
noncomputable def RealLebesgueIntegral {d:ℕ} (f: EuclideanSpace' d → ℝ) : ℝ  := if hf: RealAbsolutelyIntegrable f then hf.integ else 0

open Classical in
noncomputable def ComplexLebesgueIntegral {d:ℕ} (f: EuclideanSpace' d → ℂ) : ℂ  := if hf: ComplexAbsolutelyIntegrable f then hf.integ else 0

def RealSimpleFunction.absolutelyIntegrable_iff' {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : hf.AbsolutelyIntegrable ↔ RealAbsolutelyIntegrable f := by
  constructor
  · -- Forward: hf.AbsolutelyIntegrable → RealAbsolutelyIntegrable f
    intro hfi
    constructor
    · -- RealMeasurable f: use constant sequence
      exact ⟨fun _ => f, fun _ => hf, fun _ => tendsto_const_nhds⟩
    · -- UnsignedLebesgueIntegral (EReal.abs_fun f) < ⊤
      rw [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral.eq_simpleIntegral hf.abs]
      exact hfi
  · -- Backward: RealAbsolutelyIntegrable f → hf.AbsolutelyIntegrable
    intro ⟨_, hf_integ⟩
    rw [RealSimpleFunction.AbsolutelyIntegrable, ← LowerUnsignedLebesgueIntegral.eq_simpleIntegral hf.abs]
    exact hf_integ

def ComplexSimpleFunction.absolutelyIntegrable_iff' {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : hf.AbsolutelyIntegrable ↔ ComplexAbsolutelyIntegrable f := by
  constructor
  · -- Forward: hf.AbsolutelyIntegrable → ComplexAbsolutelyIntegrable f
    intro hfi
    constructor
    · -- ComplexMeasurable f: use constant sequence
      exact ⟨fun _ => f, fun _ => hf, fun _ => tendsto_const_nhds⟩
    · -- UnsignedLebesgueIntegral (EReal.abs_fun f) < ⊤
      rw [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral.eq_simpleIntegral hf.abs]
      exact hfi
  · -- Backward: ComplexAbsolutelyIntegrable f → hf.AbsolutelyIntegrable
    intro ⟨_, hf_integ⟩
    rw [ComplexSimpleFunction.AbsolutelyIntegrable, ← LowerUnsignedLebesgueIntegral.eq_simpleIntegral hf.abs]
    exact hf_integ

def RealSimpleFunction.AbsolutelyIntegrable.integ_eq {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) (hfi: hf.AbsolutelyIntegrable) : hf.integ = (hf.absolutelyIntegrable_iff'.mp hfi).integ := by
  -- hf.integ = (hf.pos).integ.toReal - (hf.neg).integ.toReal
  -- (hf.absolutelyIntegrable_iff'.mp hfi).integ = (UnsignedLebesgueIntegral (pos_fun f)).toReal - (UnsignedLebesgueIntegral (neg_fun f)).toReal
  simp only [RealSimpleFunction.integ, RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ]
  congr 1
  · -- (hf.pos).integ.toReal = (UnsignedLebesgueIntegral (pos_fun f)).toReal
    rw [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral.eq_simpleIntegral hf.pos]
  · -- (hf.neg).integ.toReal = (UnsignedLebesgueIntegral (neg_fun f)).toReal
    rw [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral.eq_simpleIntegral hf.neg]

def ComplexSimpleFunction.AbsolutelyIntegrable.integ_eq {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) (hfi: hf.AbsolutelyIntegrable) : hf.integ = (hf.absolutelyIntegrable_iff'.mp hfi).integ := by
  -- Both sides are defined as re.integ + I * im.integ
  simp only [ComplexSimpleFunction.integ, ComplexAbsolutelyIntegrable.integ]
  -- The key is that the re and im of the complex absolutely integrable give the same integral as the real simple function integrals
  have hf_re : RealSimpleFunction (Complex.re_fun f) := ComplexSimpleFunction.re hf
  have hf_im : RealSimpleFunction (Complex.im_fun f) := ComplexSimpleFunction.im hf
  congr 1
  · -- hf.re.integ = (hf.absolutelyIntegrable_iff'.mp hfi).re.integ
    have hre_fi : hf_re.AbsolutelyIntegrable := by
      rw [RealSimpleFunction.AbsolutelyIntegrable]
      have h := ComplexAbsolutelyIntegrable.re f (hf.absolutelyIntegrable_iff'.mp hfi)
      rw [RealAbsolutelyIntegrable, UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral.eq_simpleIntegral hf_re.abs] at h
      exact h.2
    have heq := RealSimpleFunction.AbsolutelyIntegrable.integ_eq hf_re hre_fi
    simp only [heq]
  · -- hf.im.integ = (hf.absolutelyIntegrable_iff'.mp hfi).im.integ
    have him_fi : hf_im.AbsolutelyIntegrable := by
      rw [RealSimpleFunction.AbsolutelyIntegrable]
      have h := ComplexAbsolutelyIntegrable.im f (hf.absolutelyIntegrable_iff'.mp hfi)
      rw [RealAbsolutelyIntegrable, UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral.eq_simpleIntegral hf_im.abs] at h
      exact h.2
    have heq := RealSimpleFunction.AbsolutelyIntegrable.integ_eq hf_im him_fi
    simp only [heq]

