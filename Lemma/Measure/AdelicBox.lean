import Instance.NumberField_AdelicHaar
import Def.NumberField_AdelicBox
import Lemma.Measure.AdelicHaar

open IsDedekindDomain NumberField MeasureTheory Measure
open Measure.AdelicHaar
open scoped RestrictedProduct ENNReal


noncomputable section

namespace NumberField.AdelicBox

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in

omit [NumberField K] in

theorem continuous_ringEquiv_mixedSpace :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by
  have h : (InfiniteAdeleRing.ringEquiv_mixedSpace K : InfiniteAdeleRing K → mixedEmbedding.mixedSpace K)
      = fun x => (fun (w : {w : InfinitePlace K // w.IsReal}) =>
          InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (x w.1),
        fun (w : {w : InfinitePlace K // w.IsComplex}) =>
          InfinitePlace.Completion.extensionEmbedding w.1 (x w.1)) := by
    funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply K x
  rw [h]
  refine Continuous.prodMk (continuous_pi fun w => ?_) (continuous_pi fun w => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp
      (continuous_apply w.1)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding w.1).continuous.comp
      (continuous_apply w.1)

omit [NumberField K] in

theorem properSpace_completion (v : InfinitePlace K) : ProperSpace v.Completion := by
  by_cases hv : v.IsReal
  · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.isometry.antilipschitz.properSpace
      (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous
      (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.surjective
  · have hc : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hv
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.isometry.antilipschitz.properSpace
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.continuous
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.surjective

open scoped Classical in

theorem norm_apply_le_of_isReal (x : InfiniteAdeleRing K) {v : InfinitePlace K} (hv : v.IsReal) :
    ‖x v‖ ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace K x‖ := by
  have h1 : ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal hv (x v)‖ = ‖x v‖ :=
    (AddMonoidHomClass.isometry_iff_norm _).mp
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv) (x v)
  have h2 : (InfiniteAdeleRing.ringEquiv_mixedSpace K x).1 ⟨v, hv⟩ =
      InfinitePlace.Completion.extensionEmbeddingOfIsReal hv (x v) := rfl
  rw [← h1, ← h2]
  exact (norm_le_pi_norm (InfiniteAdeleRing.ringEquiv_mixedSpace K x).1 ⟨v, hv⟩).trans
    (norm_fst_le (InfiniteAdeleRing.ringEquiv_mixedSpace K x))

open scoped Classical in

theorem norm_apply_le_of_isComplex (x : InfiniteAdeleRing K) {v : InfinitePlace K}
    (hv : v.IsComplex) : ‖x v‖ ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace K x‖ := by
  have h1 : ‖InfinitePlace.Completion.extensionEmbedding v (x v)‖ = ‖x v‖ :=
    (AddMonoidHomClass.isometry_iff_norm _).mp
      (InfinitePlace.Completion.isometry_extensionEmbedding v) (x v)
  have h2 : (InfiniteAdeleRing.ringEquiv_mixedSpace K x).2 ⟨v, hv⟩ =
      InfinitePlace.Completion.extensionEmbedding v (x v) := rfl
  rw [← h1, ← h2]
  exact (norm_le_pi_norm (InfiniteAdeleRing.ringEquiv_mixedSpace K x).2 ⟨v, hv⟩).trans
    (norm_snd_le (InfiniteAdeleRing.ringEquiv_mixedSpace K x))

open scoped Classical in

theorem exists_forall_norm_apply_le_of_mem_infiniteBox :
    ∃ r : ℝ, ∀ x ∈ infiniteBox K, ∀ v : InfinitePlace K, ‖x v‖ ≤ r := by
  obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.mp
    (ZSpan.fundamentalDomain_isBounded (mixedEmbedding.latticeBasis K))
  refine ⟨r, fun x hx v => ?_⟩
  have hx' : ‖InfiniteAdeleRing.ringEquiv_mixedSpace K x‖ ≤ r := hr _ hx
  by_cases hv : v.IsReal
  · exact (norm_apply_le_of_isReal K x hv).trans hx'
  · exact (norm_apply_le_of_isComplex K x (InfinitePlace.not_isReal_iff_isComplex.mp hv)).trans hx'

theorem exists_isCompact_infiniteBox_subset :
    ∃ S : Set (InfiniteAdeleRing K), IsCompact S ∧ infiniteBox K ⊆ S := by
  obtain ⟨r, hr⟩ := exists_forall_norm_apply_le_of_mem_infiniteBox K
  haveI : ∀ v : InfinitePlace K, ProperSpace v.Completion := fun v => properSpace_completion K v
  refine ⟨{x | ∀ v, ‖x v‖ ≤ r}, ?_, fun x hx v => hr x hx v⟩
  have : {x : InfiniteAdeleRing K | ∀ v, ‖x v‖ ≤ r} =
      Set.pi Set.univ fun v : InfinitePlace K => Metric.closedBall (0 : v.Completion) r := by
    ext x
    exact ⟨fun h v _ => mem_closedBall_zero_iff.mpr (h v),
      fun h v => mem_closedBall_zero_iff.mp (h v (Set.mem_univ v))⟩
  rw [this]
  exact isCompact_univ_pi fun v => isCompact_closedBall (0 : v.Completion) r

theorem isCompact_integralFiniteAdeles : IsCompact (integralFiniteAdeles (𝓞 K) K) := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 K),
      CompactSpace ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) := fun v =>
    inferInstanceAs (CompactSpace (v.adicCompletionIntegers K))
  have h := isCompact_range (RestrictedProduct.isOpenEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (A := fun v : HeightOneSpectrum (𝓞 K) => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    Fact.out).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

theorem isOpen_integralFiniteAdeles : IsOpen (integralFiniteAdeles (𝓞 K) K) :=
  RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (A := fun v : HeightOneSpectrum (𝓞 K) => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    Fact.out

theorem exists_isCompact_adelicBox_subset :
    ∃ C : Set (AdeleRing (𝓞 K) K), IsCompact C ∧ adelicBox K ⊆ C := by
  obtain ⟨S, hS, hsub⟩ := exists_isCompact_infiniteBox_subset K
  refine ⟨{x | x.1 ∈ S ∧ x.2 ∈ integralFiniteAdeles (𝓞 K) K}, ?_, fun x hx => ⟨hsub hx.1, hx.2⟩⟩
  have : IsCompact (S ×ˢ integralFiniteAdeles (𝓞 K) K) := hS.prod (isCompact_integralFiniteAdeles K)
  exact this

theorem measure_adelicBox_lt_top
    (μ : @Measure (AdeleRing (𝓞 K) K) (adeleBorel (𝓞 K) K))
    [IsFiniteMeasureOnCompacts μ] :
    μ (adelicBox K) < ⊤ := by
  letI := adeleBorel (𝓞 K) K
  haveI := borelSpace_adeleBorel (𝓞 K) K
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset K
  exact (measure_mono hsub).trans_lt hC.measure_lt_top

open scoped Classical in

theorem exists_isOpen_subset_adelicBox :
    ∃ U : Set (AdeleRing (𝓞 K) K), IsOpen U ∧ U.Nonempty ∧ U ⊆ adelicBox K := by
  set b := mixedEmbedding.latticeBasis K with hb
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace K with he
  let V : Set (mixedEmbedding.mixedSpace K) := {m | ∀ i, b.repr m i ∈ Set.Ioo (0 : ℝ) 1}
  have hVopen : IsOpen V := by
    have : V = ⋂ i, (fun m => b.repr m i) ⁻¹' Set.Ioo (0 : ℝ) 1 := by ext m; simp [V]
    rw [this]
    refine isOpen_iInter_of_finite fun i => IsOpen.preimage ?_ isOpen_Ioo
    exact (b.coord i).continuous_of_finiteDimensional
  have hVsub : V ⊆ ZSpan.fundamentalDomain b := fun m hm i => Set.Ioo_subset_Ico_self (hm i)
  have hVne : (e.symm (b.equivFun.symm fun _ => 1 / 2)) ∈ e ⁻¹' V := by
    show e (e.symm _) ∈ V
    rw [RingEquiv.apply_symm_apply]
    intro i
    rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
    norm_num
  have hc1 : Continuous fun x : AdeleRing (𝓞 K) K => x.1 := continuous_fst
  have hc2 : Continuous fun x : AdeleRing (𝓞 K) K => x.2 := continuous_snd
  refine ⟨{x | x.1 ∈ e ⁻¹' V ∧ x.2 ∈ integralFiniteAdeles (𝓞 K) K}, ?_, ?_, ?_⟩
  · exact ((hVopen.preimage (continuous_ringEquiv_mixedSpace K)).preimage hc1).inter
      ((isOpen_integralFiniteAdeles K).preimage hc2)
  · refine ⟨((e.symm (b.equivFun.symm fun _ => 1 / 2), 0) :
      InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K), hVne, ?_⟩
    intro v
    exact zero_mem _
  · rintro x ⟨hx1, hx2⟩
    exact ⟨hVsub hx1, hx2⟩

theorem measure_adelicBox_pos
    (μ : @Measure (AdeleRing (𝓞 K) K) (adeleBorel (𝓞 K) K))
    [μ.IsOpenPosMeasure] :
    0 < μ (adelicBox K) := by
  letI := adeleBorel (𝓞 K) K
  haveI := borelSpace_adeleBorel (𝓞 K) K
  obtain ⟨U, hU, hne, hsub⟩ := exists_isOpen_subset_adelicBox K
  exact (hU.measure_pos μ hne).trans_le (measure_mono hsub)

theorem adelicAddHaar_adelicBox_lt_top :
    adelicAddHaar (𝓞 K) K (adelicBox K) < ⊤ := by
  letI := adeleBorel (𝓞 K) K
  haveI := borelSpace_adeleBorel (𝓞 K) K
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  exact measure_adelicBox_lt_top K (adelicAddHaar (𝓞 K) K)

theorem adelicAddHaar_adelicBox_pos :
    0 < adelicAddHaar (𝓞 K) K (adelicBox K) := by
  letI := adeleBorel (𝓞 K) K
  haveI := borelSpace_adeleBorel (𝓞 K) K
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  exact measure_adelicBox_pos K (adelicAddHaar (𝓞 K) K)

end NumberField.AdelicBox

end
