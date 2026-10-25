import Lemma.Definitions.Def_MeasureTheory_ScalingDichotomy
import Lemma.Matrix.WindowedSiegelTopology
import Instance.NumberField_AdelicCentre
import Def.NumberField_AdelicVolume

open MeasureTheory Set IsDedekindDomain NumberField MeasureTheory.ScalingDichotomy
open scoped ENNReal

noncomputable section

namespace NumberField.AdelicVolume

section Adelic

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel

variable (F : Type) [Field F] [NumberField F]

open scoped Classical in


theorem archCentralUnit_snd (v₀ : InfinitePlace F) (a : (v₀.Completion)ˣ) :
    ((archCentralUnit F v₀ a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := rfl

open scoped Classical in
theorem archCentralUnit_fst_self (v₀ : InfinitePlace F) (a : (v₀.Completion)ˣ) :
    ((archCentralUnit F v₀ a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 v₀ = a := by
  sorry

open scoped Classical in
theorem archCentralUnit_fst_of_ne (v₀ : InfinitePlace F) (a : (v₀.Completion)ˣ) {v : InfinitePlace F}
    (hv : v ≠ v₀) :
    ((archCentralUnit F v₀ a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 v = 1 := by
  sorry

theorem archCentralUnit_fst_ne_zero (v₀ : InfinitePlace F) (a : (v₀.Completion)ˣ) (v : InfinitePlace F) :
    ((archCentralUnit F v₀ a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 v ≠ 0 := by
  by_cases hv : v = v₀
  · subst hv
    rw [archCentralUnit_fst_self]
    exact a.ne_zero
  · rw [archCentralUnit_fst_of_ne v₀ a hv]
    exact one_ne_zero

theorem centralScalar_val (w : (AdeleRing (𝓞 F) F)ˣ) :
    ((centralScalar (𝓞 F) F w : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = Matrix.diagonal fun _ => (w : AdeleRing (𝓞 F) F) := by
  show Matrix.scalar (Fin 2) (w : AdeleRing (𝓞 F) F) = _
  rw [Matrix.scalar_apply]

theorem centralScalar_apply_eq (w : (AdeleRing (𝓞 F) F)ˣ) (i : Fin 2) :
    ((centralScalar (𝓞 F) F w : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i i
      = (w : AdeleRing (𝓞 F) F) := by
  rw [centralScalar_val, Matrix.diagonal_apply_eq]

theorem centralScalar_apply_ne (w : (AdeleRing (𝓞 F) F)ˣ) {i j : Fin 2} (h : i ≠ j) :
    ((centralScalar (𝓞 F) F w : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j
      = 0 := by
  rw [centralScalar_val, Matrix.diagonal_apply_ne _ h]

omit [NumberField F] in

theorem norm_two_completion (v₀ : InfinitePlace F) : ‖(2 : v₀.Completion)‖ = 2 := by
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v₀).norm_map_of_map_zero (map_zero _),
    map_ofNat, RCLike.norm_ofNat]


theorem continuous_archDetNorm (v₀ : InfinitePlace F) : Continuous (archDetNorm (F := F) v₀) :=
  continuous_norm.comp ((Units.continuous_val.comp
    ((continuous_archComponent F v₀).comp (continuous_glArch (𝓞 F) F))).matrix_det)

theorem archDetNorm_pos (v₀ : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) : 0 < archDetNorm v₀ g :=
  norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero _)

theorem archDetNorm_centralScalar_mul (v₀ : InfinitePlace F) (a : (v₀.Completion)ˣ)
    (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm v₀ (centralScalar (𝓞 F) F (archCentralUnit F v₀ a) * g)
      = (‖(a : v₀.Completion)‖ * ‖(a : v₀.Completion)‖) * archDetNorm v₀ g := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]
  congr 1

  set s := archComponent F v₀ (glArch (𝓞 F) F (centralScalar (𝓞 F) F (archCentralUnit F v₀ a)))
  have hs : ∀ i j : Fin 2, (s : Matrix (Fin 2) (Fin 2) v₀.Completion) i j
      = if i = j then (a : v₀.Completion) else 0 := by
    intro i j
    simp only [s, archComponent_apply, glArch_apply]
    by_cases h : i = j
    · subst h
      rw [centralScalar_apply_eq, if_pos rfl]
      exact archCentralUnit_fst_self v₀ a
    · rw [centralScalar_apply_ne _ h, if_neg h]
      rfl
  rw [Matrix.det_fin_two, hs, hs, hs, hs]
  simp [norm_mul]

theorem measure_eq_zero_or_top_of_central_stable [MeasurableSpace (AdelicGL2 (𝓞 F) F)]
    [BorelSpace (AdelicGL2 (𝓞 F) F)] (μ : Measure (AdelicGL2 (𝓞 F) F)) [μ.IsMulLeftInvariant]
    {D : Set (AdelicGL2 (𝓞 F) F)} (hD : MeasurableSet D)
    (hstab : ∀ w : (AdeleRing (𝓞 F) F)ˣ, (w : AdeleRing (𝓞 F) F).2 = 1 →
      (∀ v : InfinitePlace F, (w : AdeleRing (𝓞 F) F).1 v ≠ 0) →
      ∀ g ∈ D, centralScalar (𝓞 F) F w * g ∈ D) :
    μ D = 0 ∨ μ D = ⊤ := by
  obtain ⟨v₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have ha₀ : (1 : ℝ) < ‖(2 : v₀.Completion)‖ := by rw [norm_two_completion]; norm_num
  have ha0 : (2 : v₀.Completion) ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans ha₀)
  set a : (v₀.Completion)ˣ := Units.mk0 (2 : v₀.Completion) ha0
  set z := centralScalar (𝓞 F) F (archCentralUnit F v₀ a)
  have hzinv : z⁻¹ = centralScalar (𝓞 F) F (archCentralUnit F v₀ a⁻¹) := by
    rw [← map_inv]
    congr 1
  have hzD : (fun g => z * g) ⁻¹' D = D := by
    ext g
    simp only [mem_preimage]
    constructor
    · intro h
      have := hstab (archCentralUnit F v₀ a⁻¹) (archCentralUnit_snd v₀ a⁻¹)
        (archCentralUnit_fst_ne_zero v₀ a⁻¹) _ h
      rwa [← hzinv, inv_mul_cancel_left] at this
    · intro h
      exact hstab (archCentralUnit F v₀ a) (archCentralUnit_snd v₀ a) (archCentralUnit_fst_ne_zero v₀ a) _ h
  refine measure_eq_zero_or_top_of_mul_preimage_eq μ (continuous_archDetNorm v₀).measurable
    (r := ‖(a : v₀.Completion)‖ * ‖(a : v₀.Completion)‖) (one_lt_mul_of_le_of_lt ha₀.le ha₀)
    (archDetNorm_centralScalar_mul v₀ a) (fun g _ => archDetNorm_pos v₀ g) hD hzD

theorem centralScalar_mul_mem_integralWindowedSiegelSet {c u : ℝ} {w : (AdeleRing (𝓞 F) F)ˣ}
    (hwf : (w : AdeleRing (𝓞 F) F).2 = 1) (hwa : ∀ v : InfinitePlace F, (w : AdeleRing (𝓞 F) F).1 v ≠ 0)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ integralWindowedSiegelSet F c u) :
    centralScalar (𝓞 F) F w * g ∈ integralWindowedSiegelSet F c u :=
  scalar_smul_mem_integralWindowedSiegelSet F hwf hwa (centralScalar_apply_eq w 0)
    (centralScalar_apply_ne w (by decide)) (centralScalar_apply_ne w (by decide))
    (centralScalar_apply_eq w 1) hg

theorem measureZeroOrInfiniteAt [MeasurableSpace (AdelicGL2 (𝓞 F) F)]
    [BorelSpace (AdelicGL2 (𝓞 F) F)] (μ : Measure (AdelicGL2 (𝓞 F) F)) [μ.IsMulLeftInvariant]
    (c u : ℝ) : MeasureZeroOrInfiniteAt F μ c u :=
  measure_eq_zero_or_top_of_central_stable μ (measurableSet_integralWindowedSiegelSet F c u)
    fun _ hwf hwa _ hg => centralScalar_mul_mem_integralWindowedSiegelSet hwf hwa hg

theorem not_pos_and_lt_top_measure_integralWindowedSiegelSet [MeasurableSpace (AdelicGL2 (𝓞 F) F)]
    [BorelSpace (AdelicGL2 (𝓞 F) F)] (μ : Measure (AdelicGL2 (𝓞 F) F)) [μ.IsMulLeftInvariant]
    (c u : ℝ) :
    ¬(0 < μ (integralWindowedSiegelSet F c u) ∧ μ (integralWindowedSiegelSet F c u) < ⊤) :=
  not_pos_and_lt_top_of_measureZeroOrInfiniteAt F (measureZeroOrInfiniteAt μ c u)

theorem measure_eq_top_of_central_stable_of_interior [MeasurableSpace (AdelicGL2 (𝓞 F) F)]
    [BorelSpace (AdelicGL2 (𝓞 F) F)] (μ : Measure (AdelicGL2 (𝓞 F) F)) [μ.IsMulLeftInvariant]
    [μ.IsOpenPosMeasure] {D : Set (AdelicGL2 (𝓞 F) F)} (hD : MeasurableSet D)
    (hstab : ∀ w : (AdeleRing (𝓞 F) F)ˣ, (w : AdeleRing (𝓞 F) F).2 = 1 →
      (∀ v : InfinitePlace F, (w : AdeleRing (𝓞 F) F).1 v ≠ 0) →
      ∀ g ∈ D, centralScalar (𝓞 F) F w * g ∈ D)
    (hU : ∃ U : Set (AdelicGL2 (𝓞 F) F), IsOpen U ∧ U.Nonempty ∧ U ⊆ D) :
    μ D = ⊤ := by
  obtain ⟨U, hUo, hUne, hUD⟩ := hU
  have hpos : 0 < μ D := (hUo.measure_pos μ hUne).trans_le (measure_mono hUD)
  exact (measure_eq_zero_or_top_of_central_stable μ hD hstab).resolve_left hpos.ne'

theorem measure_integralWindowedSiegelSet_eq_top [MeasurableSpace (AdelicGL2 (𝓞 F) F)]
    [BorelSpace (AdelicGL2 (𝓞 F) F)] (μ : Measure (AdelicGL2 (𝓞 F) F)) [μ.IsMulLeftInvariant]
    [μ.IsOpenPosMeasure] {c u : ℝ} (hc : c < 1) (hu : u ≠ 0) :
    μ (integralWindowedSiegelSet F c u) = ⊤ :=
  measure_eq_top_of_central_stable_of_interior μ (measurableSet_integralWindowedSiegelSet F c u)
    (fun _ hwf hwa _ hg => centralScalar_mul_mem_integralWindowedSiegelSet hwf hwa hg)
    (exists_isOpen_subset_integralWindowedSiegelSet F hc hu)

open NumberField.AdelicCentre in

theorem measure_image_mk_integralWindowedSiegelSet_pos {m : MeasurableSpace (AdelicPGL2 (𝓞 F) F)}
    (μ : Measure (AdelicPGL2 (𝓞 F) F)) [μ.IsOpenPosMeasure] {c u : ℝ} (hc : c < 1) (hu : u ≠ 0) :
    0 < μ (QuotientGroup.mk '' integralWindowedSiegelSet F c u) :=
  measure_image_mk_pos (𝓞 F) F μ (exists_isOpen_subset_integralWindowedSiegelSet F hc hu)

open NumberField.AdelicCentre in

theorem adelicPGLHaar_image_integralWindowedSiegelSet_pos {c u : ℝ} (hc : c < 1) (hu : u ≠ 0) :
    0 < adelicPGLHaar (𝓞 F) F (QuotientGroup.mk '' integralWindowedSiegelSet F c u) :=
  adelicPGLHaar_image_pos (𝓞 F) F (exists_isOpen_subset_integralWindowedSiegelSet F hc hu)

end Adelic

end NumberField.AdelicVolume

end
