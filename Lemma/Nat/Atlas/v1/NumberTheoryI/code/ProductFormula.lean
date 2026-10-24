import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.ProductFormula
open MeasureTheory Measure TopologicalSpace Pointwise Filter Topology MeasureTheory.Measure Metric in


/--
[compact_group_finite_measure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ProductFormula.lean)
-/
@[path]
lemma compact_group_finite_measure
  {G : Type*}
  [AddCommGroup G]
  [TopologicalSpace G]
  [CompactSpace G]
  [MeasurableSpace G]
  [BorelSpace G]
  {μ : Measure G}
  [μ.IsAddHaarMeasure] :
-- imply
  IsFiniteMeasure μ :=
-- proof
  CompactSpace.isFiniteMeasure

/--
[weil_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ProductFormula.lean)
-/
@[path]
lemma weil_uniqueness
  {G : Type*}
  [AddCommGroup G]
  [TopologicalSpace G]
  [IsTopologicalAddGroup G]
  [LocallyCompactSpace G]
  [T2Space G]
  [MeasurableSpace G]
  [BorelSpace G]
  [SecondCountableTopology G]
  {μ ν : Measure G}
  [μ.IsAddHaarMeasure]
  [ν.IsAddHaarMeasure] :
-- imply
  ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ ν = c • μ := by
-- proof
  obtain ⟨K0⟩ := PositiveCompacts.nonempty' (α := G)
  set c := ν ↑K0 / μ ↑K0 with hc_def
  have hμ_pos : μ ↑K0 ≠ 0 :=
    (measure_pos_of_nonempty_interior μ K0.interior_nonempty).ne'
  have hμ_fin : μ ↑K0 ≠ ⊤ := (IsCompact.measure_lt_top K0.isCompact).ne
  have hν_pos : ν ↑K0 ≠ 0 :=
    (measure_pos_of_nonempty_interior ν K0.interior_nonempty).ne'
  have hν_fin : ν ↑K0 ≠ ⊤ := (IsCompact.measure_lt_top K0.isCompact).ne
  refine ⟨c, ENNReal.div_ne_zero.mpr ⟨hν_pos, hμ_fin⟩,
    ENNReal.div_ne_top hν_fin hμ_pos, ?_⟩
  have hμ_eq := addHaarMeasure_unique μ K0
  have hν_eq := addHaarMeasure_unique ν K0
  rw [hμ_eq, hν_eq, smul_smul, hc_def, ENNReal.div_mul_cancel hμ_pos hμ_fin]

/--
[mulLeftContinuousAddEquiv_preimage_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ProductFormula.lean)
-/
@[path]
lemma mulLeftContinuousAddEquiv_preimage_smul
  [NormedField K]
  {a : K}
  {S : Set K}
-- given
  (ha : a ≠ 0) :
-- imply
  (mulLeftContinuousAddEquiv ha) ⁻¹' (a • S) = S := by
-- proof
  ext x
  simp only [Set.mem_preimage, mulLeftContinuousAddEquiv_apply,
    Set.mem_smul_set_iff_inv_smul_mem₀ ha, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ ha, one_mul]

/--
[mulLeftContinuousAddEquiv_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ProductFormula.lean)
-/
@[path]
lemma mulLeftContinuousAddEquiv_symm
  [NormedField K]
  {a : K}
-- given
  (ha : a ≠ 0) :
-- imply
  (mulLeftContinuousAddEquiv ha).symm = mulLeftContinuousAddEquiv (inv_ne_zero ha) := by
-- proof
  ext x; show a⁻¹ * x = a⁻¹ * x; rfl

/--
[proposition_13_16_haar_scaling](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ProductFormula.lean)
-/
@[path]
lemma proposition_13_16_haar_scaling
  {K : Type*}
  [NormedField K]
  [LocallyCompactSpace K]
  [MeasurableSpace K]
  [BorelSpace K]
  {μ : Measure K}
  [μ.IsAddHaarMeasure]
  [μ.Regular]
  {a : K}
  {S : Set K}
-- given
  (ha : a ≠ 0) :
-- imply
  μ (a • S) = ↑(addEquivAddHaarChar (mulLeftContinuousAddEquiv ha)) * μ S := by
-- proof
  have hscale := addEquivAddHaarChar_smul_preimage μ (mulLeftContinuousAddEquiv ha) (X := a • S)
  rw [mulLeftContinuousAddEquiv_preimage_smul ha S] at hscale
  rw [← hscale]; simp

/--
[distribHaarChar_eq_addEquivAddHaarChar_mulLeft](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ProductFormula.lean)
-/
@[path]
lemma distribHaarChar_eq_addEquivAddHaarChar_mulLeft
  [NormedField K]
  [LocallyCompactSpace K]
  [MeasurableSpace K]
  [BorelSpace K]
  {a : K}
-- given
  (ha : a ≠ 0) :
-- imply
  distribHaarChar K (Units.mk0 a ha) = addEquivAddHaarChar (mulLeftContinuousAddEquiv ha) := by
-- proof
  obtain ⟨s, hs_compact, hs_nhd⟩ := exists_compact_mem_nhds (0 : K)
  have hs_ne_zero : (addHaar : Measure K) s ≠ 0 := by
    obtain ⟨U, hU_sub, hU_open, h0U⟩ := mem_nhds_iff.mp hs_nhd
    exact ne_of_gt (lt_of_lt_of_le (hU_open.measure_pos addHaar ⟨0, h0U⟩) (measure_mono hU_sub))
  have hs_ne_top : (addHaar : Measure K) s ≠ ⊤ := hs_compact.measure_lt_top.ne
  apply distribHaarChar_eq_of_measure_smul_eq_mul (s := s) (μ := addHaar) hs_ne_zero hs_ne_top
  have h := addEquivAddHaarChar_smul_preimage addHaar (mulLeftContinuousAddEquiv ha)
    (X := (Units.mk0 a ha) • s)
  have preimage_eq : (mulLeftContinuousAddEquiv ha) ⁻¹' ((Units.mk0 a ha) • s) = s := by
    ext x
    simp only [Set.mem_preimage, Set.mem_smul_set]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : a * y = a * x := by
        simp only [Units.smul_def, smul_eq_mul, Units.val_mk0] at hxy; exact hxy
      exact mul_left_cancel₀ ha this ▸ hy
    · intro hx
      exact ⟨x, hx, by simp [Units.smul_def, smul_eq_mul, mulLeftContinuousAddEquiv]⟩
  rw [preimage_eq] at h
  rw [← h]; simp [ENNReal.smul_def, smul_eq_mul]

/--
[units_smul_closedBall_zero_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ProductFormula.lean)
-/
@[path]
lemma units_smul_closedBall_zero_one
  [NormedField K]
  {g : Kˣ} :
-- imply
  (g : K) • Metric.closedBall (0 : K) 1 = Metric.closedBall (0 : K) ‖(g : K)‖ := by
-- proof
  ext x
  simp only [Set.mem_smul_set, Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [smul_eq_mul]
    calc ‖(g : K) * y‖ = ‖(g : K)‖ * ‖y‖ := norm_mul _ _
    _ ≤ ‖(g : K)‖ * 1 := by gcongr
    _ = ‖(g : K)‖ := mul_one _
  · intro hx
    refine ⟨(g : K)⁻¹ * x, ?_, ?_⟩
    · show ‖(↑g)⁻¹ * x‖ ≤ 1
      calc ‖(g : K)⁻¹ * x‖ = ‖(g : K)‖⁻¹ * ‖x‖ := by rw [norm_mul, norm_inv]
      _ ≤ ‖(g : K)‖⁻¹ * ‖(g : K)‖ := by gcongr
      _ = 1 := inv_mul_cancel₀ (norm_ne_zero_iff.mpr g.ne_zero)
    · simp [smul_eq_mul]

/--
[units_smul_ball_zero_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ProductFormula.lean)
-/
@[path]
lemma units_smul_ball_zero_one
  [NormedField K]
  {g : Kˣ} :
-- imply
  (g : K) • Metric.ball (0 : K) 1 = Metric.ball (0 : K) ‖(g : K)‖ := by
-- proof
  ext x
  simp only [Set.mem_smul_set, Metric.mem_ball, dist_zero_right]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [smul_eq_mul, norm_mul]
    exact mul_lt_of_lt_one_right (norm_pos_iff.mpr g.ne_zero) hy
  · intro hx
    refine ⟨(g : K)⁻¹ * x, ?_, ?_⟩
    · simp only [norm_mul, norm_inv]
      rw [inv_mul_lt_iff₀ (norm_pos_iff.mpr g.ne_zero)]
      linarith
    · simp [smul_eq_mul]

/--
[isNormalizedAbsVal_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ProductFormula.lean)
-/
@[path]
lemma isNormalizedAbsVal_unique
  [Field K]
  [TopologicalSpace K]
  [MeasurableSpace K]
  [BorelSpace K]
  [LocallyCompactSpace K]
  [T2Space K]
  [IsTopologicalAddGroup K]
  {f g : K → ℝ}
-- given
  (hf : IsNormalizedAbsVal f)
  (hg : IsNormalizedAbsVal g) :
-- imply
  f = g := by
-- proof
  ext a
  obtain ⟨U, hU_compact, hU_nhd⟩ := exists_compact_mem_nhds (0 : K)
  set μ : Measure K := addHaar with hμ_def
  have hμ : μ.IsAddHaarMeasure := inferInstance
  have hU_pos : μ U ≠ 0 := ne_of_gt (measure_pos_of_mem_nhds μ hU_nhd)
  have hU_fin : μ U ≠ ⊤ := ne_of_lt hU_compact.measure_lt_top
  have h1 := @hf.2 μ hμ a U
  have h2 := @hg.2 μ hμ a U
  rw [h1] at h2
  have h3 : ENNReal.ofReal (f a) = ENNReal.ofReal (g a) :=
    (ENNReal.mul_left_inj hU_pos hU_fin).mp h2
  exact (ENNReal.ofReal_eq_ofReal_iff (hf.1 a) (hg.1 a)).mp h3

/--
[theorem_13_21_product_formula_global](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ProductFormula.lean)
-/
@[path]
lemma theorem_13_21_product_formula_global
  {K : Type*}
  [Field K]
  [NumberField K]
  {x : K}
-- given
  (hx : x ≠ 0) :
-- imply
  (∏ w : NumberField.InfinitePlace K, (w x) ^ w.mult) * ∏ᶠ w : NumberField.FinitePlace K, (w x) = 1 :=
-- proof
  NumberField.prod_abs_eq_one hx

/--
[mulLeftContinuousAddEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ProductFormula.lean)
-/
@[path]
private lemma mulLeftContinuousAddEquiv_apply_eq
  [NormedField K]
  {a : K}
  {x : K}
-- given
  (ha : a ≠ 0) :
-- imply
  mulLeftContinuousAddEquiv ha x = a * x := by
-- proof
  apply mulLeftContinuousAddEquiv_apply ha x


-- created on 2026-10-23
