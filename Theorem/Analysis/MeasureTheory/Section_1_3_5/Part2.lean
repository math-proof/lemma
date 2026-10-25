import Theorem.Analysis.MeasureTheory.Section_1_3_4.Part7
import Mathlib.Topology.UrysohnsLemma
import Def.Analysis.MeasureTheory.Section_1_3_5


/-- Theorem 1.3.20(ii) Approximation of $L^1$ functions by step functions -/

-- Helper: indicator of an elementary set gives a step function
private lemma elementary_indicator_is_step {d:ℕ} {E : Set (EuclideanSpace' d)}
    (hE : IsElementary E) : RealStepFunction E.indicator' := by
  obtain ⟨T, hT_disj, hE_eq⟩ := hE.partition
  refine ⟨T, fun _ => 1, ?_⟩
  ext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, one_mul]
  rw [hE_eq]
  by_cases hx : x ∈ ⋃ B ∈ T, B.toSet
  · rw [Set.indicator'_of_mem hx]
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨B, hB_mem, hx_mem⟩ := hx
    have : ∑ B : T, (B.val.toSet).indicator' x = 1 := by
      rw [Finset.sum_eq_single ⟨B, hB_mem⟩]
      · exact Set.indicator'_of_mem hx_mem
      · intro ⟨B', hB'_mem⟩ _ hne
        apply Set.indicator'_of_notMem
        intro hx_B'
        have hBB' : B ≠ B' := fun h => hne (Subtype.ext h.symm)
        exact Set.disjoint_left.mp
          (hT_disj (Finset.mem_coe.mpr hB_mem) (Finset.mem_coe.mpr hB'_mem) hBB')
          hx_mem hx_B'
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [this]
  · rw [Set.indicator'_of_notMem hx]
    symm; apply Finset.sum_eq_zero
    intro ⟨B, hB_mem⟩ _
    apply Set.indicator'_of_notMem
    intro hx_mem
    exact hx (Set.mem_iUnion₂.mpr ⟨B, hB_mem, hx_mem⟩)

-- Helper: step functions are closed under scalar multiplication
private lemma RealStepFunction.smul' {d:ℕ} {f : EuclideanSpace' d → ℝ}
    (hf : RealStepFunction f) (a : ℝ) : RealStepFunction (a • f) := by
  obtain ⟨S, c, hf_eq⟩ := hf
  exact ⟨S, fun B => a * c B, by
    rw [hf_eq]; ext x
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    congr 1; ext B; rw [mul_assoc]⟩

-- Helper: step functions are closed under addition
private lemma RealStepFunction.add' {d:ℕ} {f g : EuclideanSpace' d → ℝ}
    (hf : RealStepFunction f) (hg : RealStepFunction g) : RealStepFunction (f + g) := by
  obtain ⟨S₁, c₁, hf_eq⟩ := hf
  obtain ⟨S₂, c₂, hg_eq⟩ := hg
  refine ⟨S₁ ∪ S₂, fun B =>
    (if h : B.val ∈ S₁ then c₁ ⟨B.val, h⟩ else 0) +
    (if h : B.val ∈ S₂ then c₂ ⟨B.val, h⟩ else 0), ?_⟩
  -- Rewrite f as sum over S₁ ∪ S₂ (extending c₁ by 0 outside S₁)
  have hf_union : ∀ x, (∑ B : ↥S₁, c₁ B • (B.val.toSet).indicator') x =
      (∑ B : ↥(S₁ ∪ S₂), (if h : B.val ∈ S₁ then c₁ ⟨B.val, h⟩ else 0) •
        (B.val.toSet).indicator') x := by
    intro x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    -- Embed S₁ into S₁ ∪ S₂
    set ι : ↥S₁ → ↥(S₁ ∪ S₂) :=
      fun B => ⟨B.val, Finset.mem_union_left S₂ B.prop⟩
    have hι_inj : Function.Injective ι :=
      fun ⟨a, _⟩ ⟨b, _⟩ h => Subtype.ext (Subtype.mk.inj h)
    -- The sum over S₁ ∪ S₂ restricts to S₁
    have h_zero : ∀ B : ↥(S₁ ∪ S₂), B ∉ Set.range ι →
        (if h : B.val ∈ S₁ then c₁ ⟨B.val, h⟩ else 0) * (B.val.toSet).indicator' x = 0 := by
      intro ⟨B, hB⟩ hni
      have : B ∉ S₁ := by
        intro hB₁
        exact hni ⟨⟨B, hB₁⟩, Subtype.ext rfl⟩
      simp [this]
    rw [← Finset.sum_filter_of_ne (fun B _ => not_imp_comm.mpr (h_zero B))]
    -- Show the filter equals the image of univ under ι
    have hfilter : Finset.univ.filter (fun B : ↥(S₁ ∪ S₂) => B ∈ Set.range ι) =
        Finset.univ.image ι := by
      ext ⟨B, hB⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Set.mem_range]
    rw [hfilter, Finset.sum_image (fun _ _ _ _ h => hι_inj h)]
    apply Finset.sum_congr rfl
    intro ⟨B, hB⟩ _
    simp only [ι, hB, dite_true]
  have hg_union : ∀ x, (∑ B : ↥S₂, c₂ B • (B.val.toSet).indicator') x =
      (∑ B : ↥(S₁ ∪ S₂), (if h : B.val ∈ S₂ then c₂ ⟨B.val, h⟩ else 0) •
        (B.val.toSet).indicator') x := by
    intro x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    set ι : ↥S₂ → ↥(S₁ ∪ S₂) :=
      fun B => ⟨B.val, Finset.mem_union_right S₁ B.prop⟩
    have hι_inj : Function.Injective ι :=
      fun ⟨a, _⟩ ⟨b, _⟩ h => Subtype.ext (Subtype.mk.inj h)
    have h_zero : ∀ B : ↥(S₁ ∪ S₂), B ∉ Set.range ι →
        (if h : B.val ∈ S₂ then c₂ ⟨B.val, h⟩ else 0) * (B.val.toSet).indicator' x = 0 := by
      intro ⟨B, hB⟩ hni
      have : B ∉ S₂ := by
        intro hB₂
        exact hni ⟨⟨B, hB₂⟩, Subtype.ext rfl⟩
      simp [this]
    rw [← Finset.sum_filter_of_ne (fun B _ => not_imp_comm.mpr (h_zero B))]
    have hfilter : Finset.univ.filter (fun B : ↥(S₁ ∪ S₂) => B ∈ Set.range ι) =
        Finset.univ.image ι := by
      ext ⟨B, hB⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Set.mem_range]
    rw [hfilter, Finset.sum_image (fun _ _ _ _ h => hι_inj h)]
    apply Finset.sum_congr rfl
    intro ⟨B, hB⟩ _
    simp only [ι, hB, dite_true]
  ext x
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hf_eq, hg_eq]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ B : ↥S₁, c₁ B * (B.val.toSet).indicator' x) =
      (∑ B : ↥S₁, c₁ B • (B.val.toSet).indicator') x from by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]]
  rw [show (∑ B : ↥S₂, c₂ B * (B.val.toSet).indicator' x) =
      (∑ B : ↥S₂, c₂ B • (B.val.toSet).indicator') x from by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]]
  rw [hf_union x, hg_union x]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← add_mul, ← Finset.sum_add_distrib]

-- Helper: lift a real step function to a complex step function
private lemma RealStepFunction.toComplexStep {d:ℕ} {f : EuclideanSpace' d → ℝ}
    (hf : RealStepFunction f) : ComplexStepFunction (Real.complex_fun f) := by
  obtain ⟨S, c, hf_eq⟩ := hf
  refine ⟨S, fun B => ↑(c B), ?_⟩
  ext x
  simp only [Real.complex_fun, Complex.indicator, hf_eq]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Complex.ofReal_sum]
  congr 1; ext B
  exact Complex.ofReal_mul (c B) ((B.val.toSet).indicator' x)

-- Helper: complex step functions are closed under addition
private lemma ComplexStepFunction.add {d:ℕ} {f g : EuclideanSpace' d → ℂ}
    (hf : ComplexStepFunction f) (hg : ComplexStepFunction g) :
    ComplexStepFunction (f + g) := by
  obtain ⟨S₁, c₁, hf_eq⟩ := hf
  obtain ⟨S₂, c₂, hg_eq⟩ := hg
  refine ⟨S₁ ∪ S₂, fun B =>
    (if h : B.val ∈ S₁ then c₁ ⟨B.val, h⟩ else 0) +
    (if h : B.val ∈ S₂ then c₂ ⟨B.val, h⟩ else 0), ?_⟩
  -- Extend f-sum from S₁ to S₁ ∪ S₂
  have hf_union : ∀ x, (∑ B : ↥S₁, c₁ B • Complex.indicator (B.val.toSet)) x =
      (∑ B : ↥(S₁ ∪ S₂), (if h : B.val ∈ S₁ then c₁ ⟨B.val, h⟩ else 0) •
        Complex.indicator (B.val.toSet)) x := by
    intro x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    set ι : ↥S₁ → ↥(S₁ ∪ S₂) := fun B => ⟨B.val, Finset.mem_union_left S₂ B.prop⟩
    have hι_inj : Function.Injective ι :=
      fun ⟨a, _⟩ ⟨b, _⟩ h => Subtype.ext (Subtype.mk.inj h)
    have h_zero : ∀ B : ↥(S₁ ∪ S₂), B ∉ Set.range ι →
        (if h : B.val ∈ S₁ then c₁ ⟨B.val, h⟩ else 0) * Complex.indicator (B.val.toSet) x = 0 := by
      intro ⟨B, hB⟩ hni
      have : B ∉ S₁ := by intro hB₁; exact hni ⟨⟨B, hB₁⟩, Subtype.ext rfl⟩
      simp [this]
    rw [← Finset.sum_filter_of_ne (fun B _ => not_imp_comm.mpr (h_zero B))]
    have hfilter : Finset.univ.filter (fun B : ↥(S₁ ∪ S₂) => B ∈ Set.range ι) =
        Finset.univ.image ι := by
      ext ⟨B, hB⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image, Set.mem_range]
    rw [hfilter, Finset.sum_image (fun _ _ _ _ h => hι_inj h)]
    apply Finset.sum_congr rfl; intro ⟨B, hB⟩ _; simp only [ι, hB, dite_true]
  -- Extend g-sum from S₂ to S₁ ∪ S₂
  have hg_union : ∀ x, (∑ B : ↥S₂, c₂ B • Complex.indicator (B.val.toSet)) x =
      (∑ B : ↥(S₁ ∪ S₂), (if h : B.val ∈ S₂ then c₂ ⟨B.val, h⟩ else 0) •
        Complex.indicator (B.val.toSet)) x := by
    intro x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    set ι : ↥S₂ → ↥(S₁ ∪ S₂) := fun B => ⟨B.val, Finset.mem_union_right S₁ B.prop⟩
    have hι_inj : Function.Injective ι :=
      fun ⟨a, _⟩ ⟨b, _⟩ h => Subtype.ext (Subtype.mk.inj h)
    have h_zero : ∀ B : ↥(S₁ ∪ S₂), B ∉ Set.range ι →
        (if h : B.val ∈ S₂ then c₂ ⟨B.val, h⟩ else 0) * Complex.indicator (B.val.toSet) x = 0 := by
      intro ⟨B, hB⟩ hni
      have : B ∉ S₂ := by intro hB₂; exact hni ⟨⟨B, hB₂⟩, Subtype.ext rfl⟩
      simp [this]
    rw [← Finset.sum_filter_of_ne (fun B _ => not_imp_comm.mpr (h_zero B))]
    have hfilter : Finset.univ.filter (fun B : ↥(S₁ ∪ S₂) => B ∈ Set.range ι) =
        Finset.univ.image ι := by
      ext ⟨B, hB⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image, Set.mem_range]
    rw [hfilter, Finset.sum_image (fun _ _ _ _ h => hι_inj h)]
    apply Finset.sum_congr rfl; intro ⟨B, hB⟩ _; simp only [ι, hB, dite_true]
  ext x
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hf_eq, hg_eq]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ B : ↥S₁, c₁ B * Complex.indicator (B.val.toSet) x) =
      (∑ B : ↥S₁, c₁ B • Complex.indicator (B.val.toSet)) x from by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]]
  rw [show (∑ B : ↥S₂, c₂ B * Complex.indicator (B.val.toSet) x) =
      (∑ B : ↥S₂, c₂ B • Complex.indicator (B.val.toSet)) x from by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]]
  rw [hf_union x, hg_union x]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← add_mul, ← Finset.sum_add_distrib]

-- Helper: complex step functions are closed under scalar multiplication
private lemma ComplexStepFunction.smul {d:ℕ} {f : EuclideanSpace' d → ℂ}
    (hf : ComplexStepFunction f) (a : ℂ) : ComplexStepFunction (a • f) := by
  obtain ⟨S, c, hf_eq⟩ := hf
  exact ⟨S, fun B => a * c B, by
    rw [hf_eq]; ext x
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    congr 1; ext B; rw [mul_assoc]⟩

-- Helper: the zero function is real absolutely integrable
private lemma RealAbsolutelyIntegrable.zero_fun {d:ℕ} :
    RealAbsolutelyIntegrable (0 : EuclideanSpace' d → ℝ) := by
  constructor
  · exact ⟨fun _ => 0, fun _ => ⟨0, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, by funext x; simp [Finset.univ_eq_empty]⟩,
      fun _ => tendsto_const_nhds⟩
  · have h_zero : EReal.abs_fun (0 : EuclideanSpace' d → ℝ) = 0 := by
      funext x; simp only [EReal.abs_fun, Pi.zero_apply, norm_zero]; rfl
    rw [h_zero, UnsignedLebesgueIntegral]
    have h_simple : UnsignedSimpleFunction (0 : EuclideanSpace' d → EReal) := by
      use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
      exact ⟨fun i => Fin.elim0 i, by funext x; simp [Finset.univ_eq_empty]⟩
    rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral h_simple]
    calc h_simple.integ = 0 := UnsignedSimpleFunction.integ_zero
      _ < ⊤ := EReal.zero_lt_top

-- Helper: PreL1.norm of zero ≤ any nonneg EReal value
private lemma PreL1.norm_zero_le {d:ℕ} {a : EReal} (ha : 0 ≤ a) :
    PreL1.norm (0 : EuclideanSpace' d → ℝ) ≤ a := by
  unfold PreL1.norm
  have h_zero : EReal.abs_fun (0 : EuclideanSpace' d → ℝ) = 0 := by
    funext x; simp only [EReal.abs_fun, Pi.zero_apply, norm_zero]; rfl
  rw [h_zero, UnsignedLebesgueIntegral]
  have h_simple : UnsignedSimpleFunction (0 : EuclideanSpace' d → EReal) := by
    use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
    exact ⟨fun i => Fin.elim0 i, by funext x; simp [Finset.univ_eq_empty]⟩
  rw [LowerUnsignedLebesgueIntegral.eq_simpleIntegral h_simple,
    UnsignedSimpleFunction.integ_zero]
  exact ha

-- Helper: smul indicator is absolutely integrable when support has finite measure
private lemma RealAbsolutelyIntegrable.smul_indicator {d:ℕ}
    {E : Set (EuclideanSpace' d)} (hE : LebesgueMeasurable E)
    (c : ℝ) (hfin : c ≠ 0 → Lebesgue_measure E < ⊤) :
    RealAbsolutelyIntegrable (c • E.indicator') := by
  by_cases hc : c = 0
  · simp only [hc, zero_smul]; exact RealAbsolutelyIntegrable.zero_fun
  · have h_simple : RealSimpleFunction (c • E.indicator') :=
      ⟨1, fun _ => c, fun _ => E, fun _ => hE, by
        ext x; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_one]⟩
    exact h_simple.absolutelyIntegrable_iff'.mp (h_simple.absolutelyIntegrable_iff.mpr (by
      calc Lebesgue_measure (Support (c • E.indicator'))
          ≤ Lebesgue_outer_measure E := Lebesgue_outer_measure.mono (fun x hx => by
            rw [Support, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at hx
            by_contra h_not
            exact hx (by rw [Set.indicator'_of_notMem h_not, mul_zero]))
        _ < ⊤ := hfin hc))

-- Helper: PreL1.norm of scalar * indicator of symmDiff
private lemma PreL1.norm_smul_indicator_symmDiff_le {d:ℕ}
    {E F : Set (EuclideanSpace' d)} (hE : LebesgueMeasurable E) (hF : LebesgueMeasurable F)
    (c : ℝ) :
    PreL1.norm (c • E.indicator' - c • F.indicator') ≤
      ↑(|c|) * Lebesgue_outer_measure (symmDiff E F) := by
  have hSD : LebesgueMeasurable (symmDiff E F) :=
    (hE.inter hF.complement).union (hF.inter hE.complement)
  have hSD_simple := UnsignedSimpleFunction.indicator hSD
  have hc_nn : (Real.toEReal |c|) ≥ 0 := by exact_mod_cast abs_nonneg c
  have h_simple := hSD_simple.smul hc_nn
  -- Pointwise: |c * indicator'_E(x) - c * indicator'_F(x)| = |c| * indicator'_{E△F}(x)
  have h_pw : EReal.abs_fun (c • E.indicator' - c • F.indicator') =
      (Real.toEReal |c|) • (Real.toEReal ∘ (symmDiff E F).indicator') := by
    funext x
    simp only [EReal.abs_fun, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Function.comp]
    by_cases hxE : x ∈ E <;> by_cases hxF : x ∈ F <;>
      simp [symmDiff_def, hxE, hxF]
  -- Compute: ∫|f| = |c| • ∫indicator(E△F) = |c| * μ(E△F)
  unfold PreL1.norm UnsignedLebesgueIntegral
  rw [h_pw, LowerUnsignedLebesgueIntegral.eq_simpleIntegral h_simple,
    UnsignedSimpleFunction.integral_smul hSD_simple hc_nn,
    UnsignedSimpleFunction.integral_indicator hSD]
  unfold Lebesgue_measure; exact le_refl _

-- Helper: triangle inequality for PreL1.norm
private lemma PreL1.norm_sub_le_add {d:ℕ} {f g h : EuclideanSpace' d → ℝ}
    (hfg_ai : RealAbsolutelyIntegrable (f - g))
    (hgh_ai : RealAbsolutelyIntegrable (g - h))
    (hfg : PreL1.norm (f - g) ≤ a) (hgh : PreL1.norm (g - h) ≤ b) :
    PreL1.norm (f - h) ≤ a + b := by
  -- Key: f - h = (f - g) + (g - h), so |f-h| ≤ |f-g| + |g-h| pointwise
  have h_eq : f - h = (f - g) + (g - h) := by ext x; simp [Pi.sub_apply]
  have hfh_ai : RealAbsolutelyIntegrable (f - h) := h_eq ▸ hfg_ai.add hgh_ai
  have h_le : ∀ x, EReal.abs_fun (f - h) x ≤
      (EReal.abs_fun (f - g) + EReal.abs_fun (g - h)) x := fun x => by
    rw [h_eq]
    simp only [EReal.abs_fun, Pi.add_apply]
    rw [← EReal.coe_add]
    exact EReal.coe_le_coe_iff.mpr (norm_add_le ((f - g) x) ((g - h) x))
  have hfg_abs := RealAbsolutelyIntegrable.abs _ hfg_ai
  have hgh_abs := RealAbsolutelyIntegrable.abs _ hgh_ai
  have hfh_abs := RealAbsolutelyIntegrable.abs _ hfh_ai
  -- Monotonicity: ∫|f-h| ≤ ∫(|f-g| + |g-h|)
  have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f - h)) ≤
      UnsignedLebesgueIntegral (EReal.abs_fun (f - g) + EReal.abs_fun (g - h)) :=
    LowerUnsignedLebesgueIntegral.mono hfh_abs.1 (hfg_abs.1.add hgh_abs.1)
      (AlmostAlways.ofAlways h_le)
  -- Additivity: ∫(|f-g| + |g-h|) = ∫|f-g| + ∫|g-h|
  have h_add : UnsignedLebesgueIntegral (EReal.abs_fun (f - g) + EReal.abs_fun (g - h)) =
      UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) + UnsignedLebesgueIntegral (EReal.abs_fun (g - h)) :=
    LowerUnsignedLebesgueIntegral.add hfg_abs.1 hgh_abs.1 (hfg_abs.1.add hgh_abs.1)
  -- Combine
  unfold PreL1.norm at hfg hgh ⊢
  calc UnsignedLebesgueIntegral (EReal.abs_fun (f - h))
      ≤ UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) +
        UnsignedLebesgueIntegral (EReal.abs_fun (g - h)) := by rw [← h_add]; exact h_mono
    _ ≤ a + b := add_le_add hfg hgh

-- Main helper: every absolutely integrable simple function can be approximated by a step function
private lemma RealSimpleFunction.approx_by_step_aux {d:ℕ} {g : EuclideanSpace' d → ℝ}
    (hg_simple : RealSimpleFunction g) (hg_ai : RealAbsolutelyIntegrable g)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (h : EuclideanSpace' d → ℝ), RealStepFunction h ∧ RealAbsolutelyIntegrable h ∧
      PreL1.norm (g - h) ≤ δ := by
  obtain ⟨k, c, E, hE_meas, hg_eq⟩ := hg_simple
  by_cases hk : k = 0
  · subst hk
    have hg_zero : g = 0 := by rw [hg_eq]; funext x; simp [Finset.univ_eq_empty]
    refine ⟨0, ?_, RealAbsolutelyIntegrable.zero_fun, ?_⟩
    · exact ⟨∅, fun x => (Finset.notMem_empty x.1 x.2).elim, by simp⟩
    · rw [hg_zero, sub_zero]
      exact PreL1.norm_zero_le (EReal.coe_nonneg.mpr (le_of_lt hδ))
  · -- Case k ≠ 0: use disjoint representation and approximate each atom
    -- Step 1: Get disjoint representation of g
    have hg_simple' : RealSimpleFunction g := ⟨k, c, E, hE_meas, hg_eq⟩
    obtain ⟨n, v, A, hA_meas, hA_disj, hg_eq'⟩ := hg_simple'.disjoint_representation
    -- Step 2: Show Lebesgue_measure (Support g) < ⊤
    have hg_abs_int : hg_simple'.AbsolutelyIntegrable :=
      hg_simple'.absolutelyIntegrable_iff'.mpr hg_ai
    have hg_support_fin : Lebesgue_measure (Support g) < ⊤ :=
      hg_simple'.absolutelyIntegrable_iff.mp hg_abs_int
    -- Step 3: For each j with v j ≠ 0, A j ⊆ Support g, hence finite measure
    have hA_sub_support : ∀ j, v j ≠ 0 → A j ⊆ Support g := by
      intro j hvj x hx
      rw [Support, Set.mem_setOf_eq, hg_eq']
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single j]
      · exact mul_ne_zero hvj (Set.indicator'_of_mem hx ▸ one_ne_zero)
      · intro i _ hij
        rw [Set.indicator'_of_notMem]
        · ring
        · intro hxi
          exact absurd hxi (Set.disjoint_left.mp
            (hA_disj (Set.mem_univ j) (Set.mem_univ i) (Ne.symm hij)) hx)
      · intro h; exact absurd (Finset.mem_univ j) h
    have hA_fin : ∀ j, v j ≠ 0 → Lebesgue_measure (A j) < ⊤ := by
      intro j hvj
      calc Lebesgue_measure (A j)
          ≤ Lebesgue_outer_measure (Support g) := Lebesgue_outer_measure.mono (hA_sub_support j hvj)
        _ < ⊤ := hg_support_fin
    -- Handle n = 0 separately (g = 0 in this case)
    by_cases hn : n = 0
    · -- If n = 0, g = 0, so h = 0 works
      have hg_zero : g = 0 := by
        rw [hg_eq']; subst hn; funext x; simp [Finset.univ_eq_empty]
      refine ⟨0, ?_, RealAbsolutelyIntegrable.zero_fun, ?_⟩
      · exact ⟨∅, fun x => (Finset.notMem_empty x.1 x.2).elim, by simp⟩
      · rw [hg_zero, sub_zero]
        exact PreL1.norm_zero_le (EReal.coe_nonneg.mpr (le_of_lt hδ))
    -- Step 4: n ≠ 0, choose elementary approximations for each A j
    · have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      -- For each j with v j ≠ 0, use TFAE to get elementary F j with small symmDiff
      have hε_j : ∀ j : Fin n, 0 < δ / (↑n * (|v j| + 1)) := by
        intro j; apply div_pos hδ
        exact mul_pos hn_pos (by linarith [abs_nonneg (v j)])
      have hF_exists : ∀ j : Fin n, ∃ F : Set (EuclideanSpace' d),
          IsElementary F ∧
          (v j ≠ 0 → Lebesgue_outer_measure (symmDiff F (A j)) ≤
            ↑(δ / (↑n * (|v j| + 1)))) := by
        intro j
        by_cases hvj : v j = 0
        · exact ⟨∅, IsElementary.empty d, fun h => absurd hvj h⟩
        · have h_tfae := (LebesgueMeasurable.finite_TFAE (A j)).out 1 8
          have h_approx := h_tfae.mp ⟨hA_meas j, hA_fin j hvj⟩
          obtain ⟨F, hF_elem, hF_bound⟩ :=
            h_approx (↑(δ / (↑n * (|v j| + 1))))
              (EReal.coe_pos.mpr (hε_j j))
          exact ⟨F, hF_elem, fun _ => hF_bound⟩
      choose F hF_elem hF_bound using hF_exists
      -- Step 5: Define h = ∑ j : Fin n, v j • (F j).indicator'
      set h : EuclideanSpace' d → ℝ := ∑ j : Fin n, v j • (F j).indicator' with hh_def
      -- Each F j is elementary, so Lebesgue_outer_measure (F j) < ⊤
      have hF_fin : ∀ j : Fin n, Lebesgue_outer_measure (F j) < ⊤ := by
        intro j
        rw [Lebesgue_outer_measure.elementary (F j) (hF_elem j)]
        exact EReal.coe_lt_top _
      refine ⟨h, ?_, ?_, ?_⟩
      -- Step 6: h is a step function (by Finset induction)
      · rw [hh_def]; exact Finset.sum_induction _
          (fun f => RealStepFunction f)
          (fun f g hf hg => RealStepFunction.add' hf hg)
          ⟨∅, fun x => (Finset.notMem_empty x.1 x.2).elim, by simp⟩
          (fun j _ => RealStepFunction.smul'
            (elementary_indicator_is_step (hF_elem j)) (v j))
      -- Step 7: h is absolutely integrable
      · have hh_simple : RealSimpleFunction h :=
          ⟨n, v, fun j => F j,
           fun j => Jordan_measurable.lebesgue
             (IsElementary.jordanMeasurable (hF_elem j)),
           by rw [hh_def]⟩
        exact hh_simple.absolutelyIntegrable_iff'.mp
          ((hh_simple.absolutelyIntegrable_iff).mpr (by
            have h_support_sub : Support h ⊆ ⋃ j : Fin n, F j := by
              intro x hx
              rw [Support, Set.mem_setOf_eq] at hx
              rw [Set.mem_iUnion]
              by_contra h_not; push_neg at h_not; apply hx
              rw [hh_def]; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
              exact Finset.sum_eq_zero fun j _ =>
                by rw [Set.indicator'_of_notMem (h_not j)]; ring
            calc Lebesgue_measure (Support h)
                ≤ Lebesgue_outer_measure (⋃ j : Fin n, F j) :=
                  Lebesgue_outer_measure.mono h_support_sub
              _ ≤ ∑ j : Fin n, Lebesgue_outer_measure (F j) :=
                  Lebesgue_outer_measure.finite_union_le F
              _ < ⊤ := by
                  have : ∀ j : Fin n, Lebesgue_outer_measure (F j) =
                      ↑((hF_elem j).measure) :=
                    fun j => Lebesgue_outer_measure.elementary (F j) (hF_elem j)
                  simp_rw [this]
                  rw [← EReal.coe_finset_sum
                    (fun j _ => IsElementary.measure_nonneg (hF_elem j))]
                  exact EReal.coe_lt_top _))
      -- Step 8: Bound PreL1.norm (g - h) ≤ δ via induction on Finset
      · have hgh_eq : g - h = ∑ j : Fin n, (v j • (A j).indicator' - v j • (F j).indicator') := by
          rw [hg_eq', hh_def, ← Finset.sum_sub_distrib]
        suffices h_bound : ∀ (S : Finset (Fin n)),
            RealAbsolutelyIntegrable (∑ j ∈ S, (v j • (A j).indicator' - v j • (F j).indicator')) ∧
            PreL1.norm (∑ j ∈ S, (v j • (A j).indicator' - v j • (F j).indicator'))
            ≤ ∑ j ∈ S, (↑(|v j|) * Lebesgue_outer_measure (symmDiff (A j) (F j))) by
          rw [hgh_eq]
          have h1 := (h_bound Finset.univ).2
          calc PreL1.norm (∑ j : Fin n, (v j • (A j).indicator' - v j • (F j).indicator'))
              ≤ ∑ j : Fin n, (↑(|v j|) * Lebesgue_outer_measure (symmDiff (A j) (F j))) := h1
            _ ≤ ∑ j : Fin n, (↑(δ / ↑n) : EReal) := by
                apply Finset.sum_le_sum
                intro j _
                by_cases hvj : v j = 0
                · simp [hvj]
                  exact le_of_lt (div_pos hδ hn_pos)
                · have h_symmDiff := hF_bound j hvj
                  rw [symmDiff_comm] at h_symmDiff
                  calc ↑(|v j|) * Lebesgue_outer_measure (symmDiff (A j) (F j))
                      ≤ ↑(|v j|) * ↑(δ / (↑n * (|v j| + 1))) :=
                        mul_le_mul_of_nonneg_left h_symmDiff
                          (EReal.coe_nonneg.mpr (abs_nonneg _))
                    _ = ↑(|v j| * (δ / (↑n * (|v j| + 1)))) := by
                        rw [← EReal.coe_mul]
                    _ ≤ ↑(δ / ↑n) := by
                        rw [EReal.coe_le_coe_iff]
                        have hab : 0 < |v j| + 1 := by linarith [abs_nonneg (v j)]
                        calc |v j| * (δ / (↑n * (|v j| + 1)))
                            = |v j| * δ / (↑n * (|v j| + 1)) := by ring
                          _ ≤ (|v j| + 1) * δ / (↑n * (|v j| + 1)) := by
                              apply div_le_div_of_nonneg_right
                              · exact mul_le_mul_of_nonneg_right (by linarith) hδ.le
                              · exact (mul_pos hn_pos hab).le
                          _ = δ / ↑n := by
                              rw [mul_comm (|v j| + 1) δ, mul_div_mul_right _ _
                                (ne_of_gt hab)]
            _ = ↑δ := by
                rw [← EReal.coe_finset_sum (fun _ _ => le_of_lt (div_pos hδ hn_pos))]
                congr 1
                rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
                    mul_div_cancel₀ δ (Nat.cast_ne_zero.mpr hn)]
        -- Each term v j • (A j).indicator' - v j • (F j).indicator' is absolutely integrable
        have hterm_ai : ∀ j : Fin n, RealAbsolutelyIntegrable
            (v j • (A j).indicator' - v j • (F j).indicator') := fun j =>
          (RealAbsolutelyIntegrable.smul_indicator (hA_meas j) (v j) (hA_fin j)).sub
            (RealAbsolutelyIntegrable.smul_indicator
              (Jordan_measurable.lebesgue (IsElementary.jordanMeasurable (hF_elem j)))
              (v j) (fun _ => hF_fin j))
        -- Prove the suffices: induction on S
        intro S
        induction S using Finset.induction with
        | empty =>
          simp only [Finset.sum_empty]
          exact ⟨RealAbsolutelyIntegrable.zero_fun, PreL1.norm_zero_le le_rfl⟩
        | @insert a S haS ih =>
          rw [Finset.sum_insert haS, Finset.sum_insert haS]
          have h_single := PreL1.norm_smul_indicator_symmDiff_le (hA_meas a)
            (Jordan_measurable.lebesgue (IsElementary.jordanMeasurable (hF_elem a))) (v a)
          set f_a := v a • (A a).indicator' - v a • (F a).indicator'
          set sum_S := ∑ j ∈ S, (v j • (A j).indicator' - v j • (F j).indicator')
          have hfa_ai : RealAbsolutelyIntegrable f_a := hterm_ai a
          have hsum_ai : RealAbsolutelyIntegrable sum_S := ih.1
          -- Triangle inequality via PreL1.norm_sub_le_add
          have h_eq1 : f_a + sum_S - sum_S = f_a := by
            ext x; simp [f_a, sum_S, Pi.add_apply, Pi.sub_apply]
          have h_eq2 : sum_S - 0 = sum_S := by ext x; simp
          have h_eq3 : f_a + sum_S - 0 = f_a + sum_S := by ext x; simp
          have h_triangle : PreL1.norm (f_a + sum_S) ≤
              PreL1.norm f_a + PreL1.norm sum_S := by
            have hfg : PreL1.norm ((f_a + sum_S) - sum_S) ≤ PreL1.norm f_a := by
              rw [show (f_a + sum_S) - sum_S = f_a from h_eq1]
            have hgh : PreL1.norm (sum_S - 0) ≤ PreL1.norm sum_S := by
              rw [show sum_S - 0 = sum_S from h_eq2]
            have hfg_ai' : RealAbsolutelyIntegrable ((f_a + sum_S) - sum_S) := by
              rw [show (f_a + sum_S) - sum_S = f_a from h_eq1]; exact hfa_ai
            have hgh_ai' : RealAbsolutelyIntegrable (sum_S - 0) := by
              rw [show sum_S - 0 = sum_S from h_eq2]; exact hsum_ai
            calc PreL1.norm (f_a + sum_S)
                = PreL1.norm ((f_a + sum_S) - 0) := by congr 1; exact h_eq3.symm
              _ ≤ PreL1.norm f_a + PreL1.norm sum_S :=
                  PreL1.norm_sub_le_add hfg_ai' hgh_ai' hfg hgh
          constructor
          · exact hfa_ai.add hsum_ai
          · calc PreL1.norm (f_a + sum_S)
                ≤ PreL1.norm f_a + PreL1.norm sum_S := h_triangle
              _ ≤ (↑(|v a|) * Lebesgue_outer_measure (symmDiff (A a) (F a))) +
                  (∑ j ∈ S, (↑(|v j|) * Lebesgue_outer_measure (symmDiff (A j) (F j)))) :=
                  add_le_add h_single ih.2

theorem RealAbsolutelyIntegrable.approx_by_step {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf : RealAbsolutelyIntegrable f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : EuclideanSpace' d → ℝ), RealStepFunction g ∧ RealAbsolutelyIntegrable g ∧
        PreL1.norm (f - g) ≤ ε := by
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨g₁, hg₁_simple, hg₁_ai, hg₁_norm⟩ := hf.approx_by_simple (ε / 2) hε2
  obtain ⟨g₂, hg₂_step, hg₂_ai, hg₂_norm⟩ :=
    RealSimpleFunction.approx_by_step_aux hg₁_simple hg₁_ai (ε / 2) hε2
  refine ⟨g₂, hg₂_step, hg₂_ai, ?_⟩
  have h_combined := PreL1.norm_sub_le_add (hf.sub hg₁_ai) (hg₁_ai.sub hg₂_ai) hg₁_norm hg₂_norm
  calc PreL1.norm (f - g₂) ≤ ↑(ε / 2) + ↑(ε / 2) := h_combined
    _ = (ε : EReal) := by rw [← EReal.coe_add]; congr 1; linarith

theorem ComplexAbsolutelyIntegrable.approx_by_step {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf : ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ), ComplexStepFunction g ∧ ComplexAbsolutelyIntegrable g ∧
    PreL1.norm (f - g) ≤ ε := by
  -- Approximate real and imaginary parts within ε/2
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨g_re, hg_re_step, hg_re_ai, hg_re_norm⟩ :=
    (ComplexAbsolutelyIntegrable.re f hf).approx_by_step (ε / 2) hε2
  obtain ⟨g_im, hg_im_step, hg_im_ai, hg_im_norm⟩ :=
    (ComplexAbsolutelyIntegrable.im f hf).approx_by_step (ε / 2) hε2
  -- Construct complex approximation g = ↑g_re + I • ↑g_im
  set g : EuclideanSpace' d → ℂ :=
    Real.complex_fun g_re + Complex.I • Real.complex_fun g_im with hg_def
  have hg_re_eq : Complex.re_fun g = g_re := by
    ext x; simp only [Complex.re_fun, hg_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Real.complex_fun, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]; ring
  have hg_im_eq : Complex.im_fun g = g_im := by
    ext x; simp only [Complex.im_fun, hg_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Real.complex_fun, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re]; ring
  -- g is a complex step function
  have hg_step : ComplexStepFunction g :=
    ComplexStepFunction.add
      (RealStepFunction.toComplexStep hg_re_step)
      (ComplexStepFunction.smul (RealStepFunction.toComplexStep hg_im_step) Complex.I)
  -- g is absolutely integrable
  have hg_ai : ComplexAbsolutelyIntegrable g := by
    apply (ComplexAbsolutelyIntegrable.iff g).mpr
    exact ⟨hg_re_eq ▸ hg_re_ai, hg_im_eq ▸ hg_im_ai⟩
  refine ⟨g, hg_step, hg_ai, ?_⟩
  -- Norm bound: PreL1.norm (f - g) ≤ ε
  show UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≤ (ε : EReal)
  have hfg_re : Complex.re_fun (f - g) = Complex.re_fun f - g_re := by
    ext x; simp only [Complex.re_fun, hg_def, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Real.complex_fun, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]; ring
  have hfg_im : Complex.im_fun (f - g) = Complex.im_fun f - g_im := by
    ext x; simp only [Complex.im_fun, hg_def, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Real.complex_fun, Complex.sub_im, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]; ring
  have h_bound : ∀ x, EReal.abs_fun (f - g) x ≤
      (EReal.abs_fun (Complex.re_fun (f - g)) + EReal.abs_fun (Complex.im_fun (f - g))) x :=
    fun x => by
      simp only [EReal.abs_fun, Complex.re_fun, Complex.im_fun, Pi.add_apply]
      rw [← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (by
        calc ‖(f - g) x‖ ≤ |((f - g) x).re| + |((f - g) x).im| :=
            Complex.norm_le_abs_re_add_abs_im _
          _ = ‖((f - g) x).re‖ + ‖((f - g) x).im‖ := by rw [Real.norm_eq_abs, Real.norm_eq_abs])
  have hfg_ai := hf.sub hg_ai
  have hfg_re_ai := ComplexAbsolutelyIntegrable.re (f - g) hfg_ai
  have hfg_im_ai := ComplexAbsolutelyIntegrable.im (f - g) hfg_ai
  have h_mono : UnsignedLebesgueIntegral (EReal.abs_fun (f - g)) ≤
      UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun (f - g)) +
                                EReal.abs_fun (Complex.im_fun (f - g))) :=
    LowerUnsignedLebesgueIntegral.mono hfg_ai.abs.1
      (hfg_re_ai.abs.1.add hfg_im_ai.abs.1) (AlmostAlways.ofAlways h_bound)
  have h_add : UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun (f - g)) +
      EReal.abs_fun (Complex.im_fun (f - g))) =
      UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun (f - g))) +
      UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun (f - g))) :=
    LowerUnsignedLebesgueIntegral.add hfg_re_ai.abs.1 hfg_im_ai.abs.1
      (hfg_re_ai.abs.1.add hfg_im_ai.abs.1)
  rw [h_add] at h_mono
  rw [show EReal.abs_fun (Complex.re_fun (f - g)) =
        EReal.abs_fun (Complex.re_fun f - g_re) from by rw [hfg_re],
      show EReal.abs_fun (Complex.im_fun (f - g)) =
        EReal.abs_fun (Complex.im_fun f - g_im) from by rw [hfg_im]] at h_mono
  calc UnsignedLebesgueIntegral (EReal.abs_fun (f - g))
      ≤ UnsignedLebesgueIntegral (EReal.abs_fun (Complex.re_fun f - g_re)) +
        UnsignedLebesgueIntegral (EReal.abs_fun (Complex.im_fun f - g_im)) := h_mono
    _ ≤ (↑(ε / 2) : EReal) + (↑(ε / 2) : EReal) := add_le_add hg_re_norm hg_im_norm
    _ = (ε : EReal) := by rw [← EReal.coe_add]; congr 1; linarith

