import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.LieGroups.code.PlancherelCompact
open MeasureTheory PlancherelCompact
open scoped Topology Manifold


/--
[convolutionOp_eq_kernel_integral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma convolutionOp_eq_kernel_integral
  [Group K]
  [TopologicalSpace K]
  [CompactSpace K]
  [MeasureSpace K]
  {f : K → ℂ}
  {ψ : K → ℂ}
  {x : K} :
-- imply
  convolutionOp f ψ x = ∫ y, convolutionKernel f x y * ψ y := by
-- proof
  rfl

/--
[convolutionKernel_diag_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma convolutionKernel_diag_eq
  [Group K]
  {f : K → ℂ}
  {x : K} :
-- imply
  convolutionKernel f x x = f 1 := by
-- proof
  unfold convolutionKernel
  simp [mul_inv_cancel]

/--
[convolutionKernelDiag_eq_const](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma convolutionKernelDiag_eq_const
  [Group K]
  [TopologicalSpace K]
  [CompactSpace K]
  [MeasureSpace K]
  {f : K → ℂ} :
-- imply
  convolutionKernelDiagIntegral f = ∫ _ : K, f 1 := by
-- proof
  unfold convolutionKernelDiagIntegral
  simp [convolutionKernel_diag_eq]

/--
[convolutionKernelDiagIntegral_eq_eval_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma convolutionKernelDiagIntegral_eq_eval_one
  [Group K]
  [TopologicalSpace K]
  [CompactSpace K]
  [MeasureSpace K]
  [BorelSpace K]
  [IsProbabilityMeasure (volume : Measure K)]
  {f : K → ℂ} :
-- imply
  convolutionKernelDiagIntegral f = f 1 := by
-- proof
  rw [convolutionKernelDiag_eq_const]
  simp [integral_const]

/--
[exists_dirac_sequence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma exists_dirac_sequence
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  [LocallyCompactSpace G]
  [SecondCountableTopology G]
  [MeasureSpace G]
  [BorelSpace G]
  [Measure.IsHaarMeasure (volume : Measure G)] :
-- imply
  ∃ (φ : ℕ → G → ℝ), (∀ (n : ℕ), Continuous (φ n)) ∧ (∀ (n : ℕ), HasCompactSupport (φ n)) ∧ (∀ (f : G → ℂ), Continuous f → HasCompactSupport f → Filter.Tendsto (fun (n : ℕ) => ∫ (g : G), (φ n g : ℂ) * f g) Filter.atTop (nhds (f 1))) := by
-- proof
  obtain ⟨U, hU⟩ := (nhds (1 : G)).exists_antitone_basis
  have hbump : ∀ n, ∃ (ψ : C(G, ℝ)),
    ψ 1 = 1 ∧ IsCompact (tsupport ψ) ∧ tsupport ψ ⊆ U n ∧
    (∀ x, ψ x ∈ Set.Icc 0 1) := by
    intro n
    have hUn : U n ∈ nhds (1 : G) := hU.toHasBasis.mem_of_mem trivial
    obtain ⟨V, hV_sub, hV_open, h1V⟩ := mem_nhds_iff.mp hUn
    obtain ⟨f, hf_eq, hf_compact, hf_supp, hf_range⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen isCompact_singleton hV_open
        (Set.singleton_subset_iff.mpr h1V)
    exact ⟨f, by simp [hf_eq (Set.mem_singleton 1)],
      hf_compact, hf_supp.trans hV_sub, hf_range⟩
  choose ψ hψ_one hψ_compact hψ_supp hψ_range using hbump
  have hψ_nonneg : ∀ n, 0 ≤ (ψ n : G → ℝ) := fun n x => (hψ_range n x).1
  have hψ_int_pos : ∀ n, (0 : ℝ) < ∫ x, (ψ n) x := by
    intro n
    exact (ψ n).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hψ_compact n) (hψ_nonneg n) (by rw [hψ_one n]; exact one_ne_zero)
  set φ : ℕ → G → ℝ := fun n x => (∫ g, (ψ n) g)⁻¹ * (ψ n) x with φ_def
  have hφ_int : ∀ n, ∫ x, φ n x = 1 := by
    intro n; simp only [φ_def, ← smul_eq_mul, integral_smul]
    exact inv_mul_cancel₀ (ne_of_gt (hψ_int_pos n))
  have hψ_vanish : ∀ n x, x ∉ U n → (ψ n) x = 0 := by
    intro n x hx; by_contra h
    exact hx (hψ_supp n (subset_tsupport _ (Function.mem_support.mpr h)))
  refine ⟨φ, ?_, ?_, ?_⟩
  · exact fun n => continuous_const.mul (ψ n).continuous
  · intro n
    have : Function.support (φ n) ⊆ Function.support (ψ n : G → ℝ) := by
      intro x hx; simp only [Function.mem_support, φ_def] at hx ⊢
      intro hfx; exact hx (by simp [hfx])
    exact (hψ_compact n).of_isClosed_subset (isClosed_tsupport _) (closure_mono this)
  · intro f h_cont h_supp
    simp_rw [show ∀ n g, (φ n g : ℂ) * f g = φ n g • f g from
      fun n g => (Complex.real_smul).symm]
    obtain ⟨K, hK_compact, hK_nhds⟩ := exists_compact_mem_nhds (1 : G)
    obtain ⟨V, hV_sub, hV_open, h1V⟩ := mem_nhds_iff.mp hK_nhds
    apply tendsto_integral_peak_smul_of_integrable_of_tendsto
      hV_open.measurableSet (hV_open.mem_nhds h1V)
      (ne_of_lt (lt_of_le_of_lt (measure_mono hV_sub) hK_compact.measure_lt_top))
    · exact Filter.Eventually.of_forall fun n x =>
      mul_nonneg (inv_nonneg.mpr (hψ_int_pos n).le) (hψ_nonneg n x)
    · intro u hu h1u
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := hU.toHasBasis.mem_iff.mp (hu.mem_nhds h1u)
      filter_upwards [Filter.Ici_mem_atTop N] with n hn x hx
      simp only [Pi.zero_apply, Real.dist_eq]
      simp [φ_def, hψ_vanish n x (fun h => hx (hN.2 (hU.antitone (Set.mem_Ici.mp hn) h))), hε]
    · obtain ⟨N, hN⟩ := hU.toHasBasis.mem_iff.mp (hV_open.mem_nhds h1V)
      refine tendsto_atTop_of_eventually_const (i₀ := N) (fun n hn => ?_)
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_]
      · exact hφ_int n
      · simp [φ_def, hψ_vanish n x (fun h => hx (hN.2 (hU.antitone hn h)))]
    · exact Filter.Eventually.of_forall fun n =>
      (continuous_const.mul (ψ n).continuous).aestronglyMeasurable
    · exact h_cont.integrable_of_hasCompactSupport h_supp
    · exact h_cont.continuousAt
set_option maxHeartbeats 3200000 in

/--
[exists_smooth_dirac_sequence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma exists_smooth_dirac_sequence
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  [LocallyCompactSpace G]
  [SecondCountableTopology G]
  [MeasureSpace G]
  [BorelSpace G]
  [Measure.IsHaarMeasure (volume : Measure G)]
  [NormedAddCommGroup EG]
  [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG]
  [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG}
  [ChartedSpace HG G]
  [LieGroup IG ⊤ G]
  [T2Space G] :
-- imply
  ∃ (φ : ℕ → G → ℝ), (∀ (n : ℕ), ContMDiff IG 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞)) (φ n)) ∧ (∀ (n : ℕ), HasCompactSupport (φ n)) ∧ (∀ (f : G → ℂ), Continuous f → HasCompactSupport f → Filter.Tendsto (fun (n : ℕ) => ∫ (g : G), (φ n g : ℂ) * f g) Filter.atTop (nhds (f 1))) := by
-- proof
  haveI : IsManifold IG (↑(⊤ : ℕ∞)) G := IsManifold.of_le le_top
  obtain ⟨U, hU⟩ := (nhds (1 : G)).exists_antitone_basis
  have hbump : ∀ n, ∃ (ψ : SmoothBumpFunction IG (1 : G)),
    tsupport (ψ : G → ℝ) ⊆ U n := by
    intro n
    have hUn : U n ∈ nhds (1 : G) := hU.toHasBasis.mem_of_mem trivial
    obtain ⟨ψ, _, hψ_supp⟩ :=
      (SmoothBumpFunction.nhds_basis_tsupport (I := IG) (1 : G)).mem_iff.mp hUn
    exact ⟨ψ, hψ_supp⟩
  choose ψ hψ_supp using hbump
  have hψ_nonneg : ∀ n, 0 ≤ (ψ n : G → ℝ) := fun n x => (ψ n).nonneg
  have hψ_one : ∀ n, (ψ n : G → ℝ) (1 : G) = 1 := fun n => (ψ n).eq_one
  have hψ_cont : ∀ n, Continuous (ψ n : G → ℝ) := fun n => (ψ n).continuous
  have hψ_compact : ∀ n, HasCompactSupport (ψ n : G → ℝ) := fun n => (ψ n).hasCompactSupport
  have hψ_int_pos : ∀ n, (0 : ℝ) < ∫ x, (ψ n : G → ℝ) x := by
    intro n
    exact (hψ_cont n).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hψ_compact n) (hψ_nonneg n) (by rw [hψ_one n]; exact one_ne_zero)
  set φ : ℕ → G → ℝ := fun n x =>
    (∫ g, (ψ n : G → ℝ) g)⁻¹ * (ψ n : G → ℝ) x with φ_def
  have hφ_int : ∀ n, ∫ x, φ n x = 1 := by
    intro n; simp only [φ_def, ← smul_eq_mul, integral_smul]
    exact inv_mul_cancel₀ (ne_of_gt (hψ_int_pos n))
  have hψ_vanish : ∀ n x, x ∉ U n → (ψ n : G → ℝ) x = 0 := by
    intro n x hx; by_contra h
    exact hx (hψ_supp n (subset_tsupport _ (Function.mem_support.mpr h)))
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro n
    have h : ContMDiff IG 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞)) (ψ n : G → ℝ) :=
      SmoothBumpFunction.contMDiff (ψ n)
    have hconst : ContMDiff IG 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞))
      (fun _ : G => (∫ g, (ψ n : G → ℝ) g)⁻¹) :=
      (contMDiff_const (n := ⊤)).of_le le_top
    change ContMDiff IG 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞))
      (fun x => (∫ g, (ψ n : G → ℝ) g)⁻¹ • (ψ n : G → ℝ) x)
    exact hconst.smul h
  · intro n
    have : Function.support (φ n) ⊆ Function.support (ψ n : G → ℝ) := by
      intro x hx; simp only [Function.mem_support, φ_def] at hx ⊢
      intro hfx; exact hx (by simp [hfx])
    exact (hψ_compact n).of_isClosed_subset (isClosed_tsupport _) (closure_mono this)
  · intro f h_cont h_supp
    simp_rw [show ∀ n g, (φ n g : ℂ) * f g = φ n g • f g from
      fun n g => (Complex.real_smul).symm]
    obtain ⟨K, hK_compact, hK_nhds⟩ := exists_compact_mem_nhds (1 : G)
    obtain ⟨V, hV_sub, hV_open, h1V⟩ := mem_nhds_iff.mp hK_nhds
    apply tendsto_integral_peak_smul_of_integrable_of_tendsto
      hV_open.measurableSet (hV_open.mem_nhds h1V)
      (ne_of_lt (lt_of_le_of_lt (measure_mono hV_sub) hK_compact.measure_lt_top))
    · exact Filter.Eventually.of_forall fun n x =>
      mul_nonneg (inv_nonneg.mpr (hψ_int_pos n).le) (hψ_nonneg n x)
    · intro u hu h1u
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := hU.toHasBasis.mem_iff.mp (hu.mem_nhds h1u)
      filter_upwards [Filter.Ici_mem_atTop N] with n hn x hx
      simp only [Pi.zero_apply, Real.dist_eq]
      simp [φ_def, hψ_vanish n x
        (fun h => hx (hN.2 (hU.antitone (Set.mem_Ici.mp hn) h))), hε]
    · obtain ⟨N, hN⟩ := hU.toHasBasis.mem_iff.mp (hV_open.mem_nhds h1V)
      refine tendsto_atTop_of_eventually_const (i₀ := N) (fun n hn => ?_)
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_]
      · exact hφ_int n
      · simp [φ_def, hψ_vanish n x (fun h => hx (hN.2 (hU.antitone hn h)))]
    · exact Filter.Eventually.of_forall fun n =>
      (continuous_const.mul (hψ_cont n)).aestronglyMeasurable
    · exact h_cont.integrable_of_hasCompactSupport h_supp
    · exact h_cont.continuousAt
set_option maxHeartbeats 1600000 in

/--
[cc_seq_converges_to_dirac](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma cc_seq_converges_to_dirac
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  [LocallyCompactSpace G]
  [SecondCountableTopology G]
  [MeasureSpace G]
  [BorelSpace G]
  [Measure.IsHaarMeasure (volume : Measure G)]
  {g₀ : G} :
-- imply
  ∃ (ψ : ℕ → G → ℝ), (∀ (n : ℕ), Continuous (ψ n)) ∧ (∀ (n : ℕ), HasCompactSupport (ψ n)) ∧ (∀ (f : G → ℂ), Continuous f → HasCompactSupport f → Filter.Tendsto (fun (n : ℕ) => ∫ (g : G), (ψ n g : ℂ) * f g) Filter.atTop (nhds (f g₀))) := by
-- proof
  obtain ⟨φ, hφ_cont, hφ_supp, hφ_conv⟩ := @exists_dirac_sequence G _ _ _ _ _ _ _ _
  refine ⟨fun n g => φ n (g₀⁻¹ * g), ?_, ?_, ?_⟩
  · intro n
    exact (hφ_cont n).comp (continuous_const.mul continuous_id)
  · intro n
    exact (hφ_supp n).comp_homeomorph (Homeomorph.mulLeft g₀⁻¹)
  · intro f hf_cont hf_supp
    have key : ∀ n, ∫ g, (φ n (g₀⁻¹ * g) : ℂ) * f g = ∫ h, (φ n h : ℂ) * f (g₀ * h) := by
      intro n
      rw [show (fun g => (φ n (g₀⁻¹ * g) : ℂ) * f g) =
        fun g => ((fun h => (φ n h : ℂ) * f (g₀ * h)) (g₀⁻¹ * g)) from by
        ext g; simp [mul_inv_cancel_left]]
      exact @MeasureTheory.integral_mul_left_eq_self G ℂ _ _ _ (volume) _ _ _
        (fun h => (φ n h : ℂ) * f (g₀ * h)) g₀⁻¹
    simp_rw [key]
    have hfg : Continuous (f ∘ (g₀ * ·)) := hf_cont.comp (continuous_const.mul continuous_id)
    have hfg_supp : HasCompactSupport (f ∘ (g₀ * ·)) :=
      hf_supp.comp_homeomorph (Homeomorph.mulLeft g₀)
    have := hφ_conv (f ∘ (g₀ * ·)) hfg hfg_supp
    simp only [Function.comp, mul_one] at this
    convert this using 1

/--
[concreteDiracEmbed_apply_eq'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma concreteDiracEmbed_apply_eq'
  [TopologicalSpace X]
  {σ : X →₀ ℂ}
  {f : C(X, ℂ)} :
-- imply
  (concreteDiracEmbed X σ) f = ∑ x ∈ σ.support, σ x * f x := by
-- proof
  unfold concreteDiracEmbed
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  change topDualPairing ℂ C(X, ℂ) (∑ x ∈ σ.support, σ x • concreteDirac X x) f
    = ∑ x ∈ σ.support, σ x * f x
  rw [map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun _ _ => rfl)

/--
[finitely_supported_seq_dense_in_measures](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma finitely_supported_seq_dense_in_measures
  [TopologicalSpace X]
  [LocallyCompactSpace X]
  [SecondCountableTopology X]
  [T2Space X]
  {μ : C(X, ℂ) →L[ℂ] ℂ} :
-- imply
  ∃ (μ_seq : ℕ → C(X, ℂ) →L[ℂ] ℂ), (∀ n, ∃ (S : Finset X) (c : X → ℂ), ∀ (f : C(X, ℂ)), μ_seq n f = ∑ x ∈ S, c x * f x) ∧ (∀ (f : C(X, ℂ)), Filter.Tendsto (fun n => μ_seq n f) Filter.atTop (nhds (μ f))) := by
-- proof
  obtain ⟨σ_seq, hconv⟩ := lemma_3_4_seq_dense_concrete X (μ : WeakDual ℂ C(X, ℂ))
  refine ⟨fun n => concreteDiracEmbed X (σ_seq n), ?_, ?_⟩
  · intro n
    exact ⟨(σ_seq n).support, fun x => σ_seq n x,
      fun f => concreteDiracEmbed_apply_eq' (σ_seq n) f⟩
  · intro f
    exact ((WeakBilin.eval_continuous _ f).tendsto _).comp hconv

/--
[compactly_supported_measure_to_clm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma compactly_supported_measure_to_clm
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  [LocallyCompactSpace G]
  [SecondCountableTopology G]
  [T2Space G]
  [MeasureSpace G]
  [BorelSpace G]
  [Measure.IsHaarMeasure (volume : Measure G)]
  {μ : Measure G}
  [IsFiniteMeasureOnCompacts μ]
-- given
  (hμ : IsCompact μ.support) :
-- imply
  ∃ (Φ : C(G, ℂ) →L[ℂ] ℂ), ∀ (f : C(G, ℂ)), Φ f = ∫ (g : G), f g ∂μ := by
-- proof
  have hfin : IsFiniteMeasure μ := by
    constructor
    calc μ Set.univ = μ (μ.support ∪ μ.supportᶜ) := by rw [Set.union_compl_self]
    _ ≤ μ μ.support + μ μ.supportᶜ := measure_union_le _ _
    _ = μ μ.support + 0 := by rw [μ.measure_compl_support]
    _ = μ μ.support := by ring
    _ < ⊤ := hμ.measure_lt_top
  have hrestr : μ = μ.restrict μ.support := by
    symm; rw [Measure.restrict_eq_self_of_ae_mem]
    rw [ae_iff]; exact μ.measure_compl_support
  have hint : ∀ (f : C(G, ℂ)), Integrable (fun g => f g) μ := by
    intro f
    rw [hrestr]
    exact ContinuousOn.integrableOn_compact hμ f.continuous.continuousOn
  let linMap : C(G, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ g, f g ∂μ
      map_add' := fun f₁ f₂ => by
        simp only [ContinuousMap.add_apply]
        exact integral_add (hint f₁) (hint f₂)
      map_smul' := fun c f => by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply]
        exact integral_smul c _ }
  have hcont : Continuous linMap := by
    apply continuous_iff_continuousAt.mpr
    intro f₀
    apply MeasureTheory.continuousAt_of_dominated
      (F := fun (f : C(G, ℂ)) (g : G) => f g)
      (bound := fun g => ‖f₀ g‖ + 1)
    ·
      filter_upwards with f
      exact (map_continuous f).aestronglyMeasurable
    ·
      have hbasis := nhds_basis_uniformity
        ContinuousMap.hasBasis_compactConvergenceUniformity (x := f₀)
      rw [hbasis.eventually_iff]
      refine ⟨(μ.support, {p : ℂ × ℂ | dist p.1 p.2 < 1}),
        ⟨hμ, Metric.dist_mem_uniformity (by norm_num : (1:ℝ) > 0)⟩, ?_⟩
      intro f hf
      simp only [Set.mem_setOf_eq] at hf
      rw [ae_iff]
      apply le_antisymm _ (zero_le _)
      calc μ {g | ¬(‖f g‖ ≤ ‖f₀ g‖ + 1)} ≤ μ μ.supportᶜ := by
        apply measure_mono
        intro g hg
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hg ⊢
        intro hgs
        have hdist : dist (f g) (f₀ g) < 1 := hf g hgs
        rw [Complex.dist_eq] at hdist
        have : ‖f g‖ ≤ ‖f₀ g‖ + ‖f g - f₀ g‖ := by
          calc ‖f g‖ = ‖f₀ g + (f g - f₀ g)‖ := by ring_nf
          _ ≤ ‖f₀ g‖ + ‖f g - f₀ g‖ := norm_add_le _ _
        linarith
      _ = 0 := μ.measure_compl_support
    ·
      apply Integrable.add (hint f₀ |>.norm)
      exact integrable_const 1
    ·
      exact Filter.Eventually.of_forall (fun g => (continuous_eval_const g).continuousAt)
  exact ⟨⟨linMap, hcont⟩, fun f => rfl⟩

/--
[cc_seq_dense_approx_finsupp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma cc_seq_dense_approx_finsupp
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  [LocallyCompactSpace G]
  [SecondCountableTopology G]
  [T2Space G]
  [MeasureSpace G]
  [BorelSpace G]
  [Measure.IsHaarMeasure (volume : Measure G)]
  {μ : Measure G}
  [IsFiniteMeasureOnCompacts μ]
-- given
  (hμ : IsCompact μ.support) :
-- imply
  ∃ (S : ℕ → Finset G) (c : ℕ → G → ℂ), ∀ (f : G → ℂ), Continuous f → Filter.Tendsto (fun n => ∑ x ∈ S n, c n x * f x) Filter.atTop (nhds (∫ (g : G), f g ∂μ)) := by
-- proof
  obtain ⟨Φ, hΦ⟩ := compactly_supported_measure_to_clm μ hμ
  obtain ⟨μ_seq, hfin, hconv⟩ := finitely_supported_seq_dense_in_measures Φ
  choose S c hSc using hfin
  refine ⟨S, c, fun f hf => ?_⟩
  let f' : C(G, ℂ) := ⟨f, hf⟩
  have hconv_f := hconv f'
  rw [show (∫ (g : G), f g ∂μ) = Φ f' from (hΦ f').symm]
  convert hconv_f using 1
  ext n
  exact (hSc n f').symm

/--
[hasCompactSupport_finset_sum'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma hasCompactSupport_finset_sum'
  [TopologicalSpace α]
  [AddCommMonoid β]
  [TopologicalSpace β]
  {F : Finset ι}
  {f : ι → α → β}
-- given
  (hf : ∀ i ∈ F, HasCompactSupport (f i)) :
-- imply
  HasCompactSupport (fun x => ∑ i ∈ F, f i x) := by
-- proof
  induction F using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasCompactSupport.zero
  | cons i s his ih =>
    have : (fun x => ∑ j ∈ Finset.cons i s his, f j x) =
      f i + (fun x => ∑ j ∈ s, f j x) := by
      ext x; simp [Finset.sum_cons, Pi.add_apply]
    rw [this]
    exact (hf i (Finset.mem_cons_self i s)).add
      (ih (fun j hj => hf j (Finset.mem_cons.mpr (Or.inr hj))))

/--
[finsupp_in_seq_closure_cc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma finsupp_in_seq_closure_cc
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  [LocallyCompactSpace G]
  [SecondCountableTopology G]
  [MeasureSpace G]
  [BorelSpace G]
  [Measure.IsHaarMeasure (volume : Measure G)]
  {F : Finset G}
  {a : G → ℂ}
-- given
  (dirac_approx : ∀ (g₀ : G), ∃ (ψ : ℕ → G → ℝ), (∀ (n : ℕ), Continuous (ψ n)) ∧ (∀ (n : ℕ), HasCompactSupport (ψ n)) ∧ (∀ (f : G → ℂ), Continuous f → HasCompactSupport f → Filter.Tendsto (fun (n : ℕ) => ∫ (g : G), (ψ n g : ℂ) * f g) Filter.atTop (nhds (f g₀)))) :
-- imply
  ∃ (ψ : ℕ → G → ℂ), (∀ n, Continuous (ψ n)) ∧ (∀ n, HasCompactSupport (ψ n)) ∧ (∀ f : G → ℂ, Continuous f → HasCompactSupport f → Filter.Tendsto (fun n => ∫ g, ψ n g * f g) Filter.atTop (nhds (∑ x ∈ F, a x * f x))) := by
-- proof
  choose ψ_pt hcont_pt hsupp_pt hconv_pt using fun x => dirac_approx x
  refine ⟨fun n g => ∑ x ∈ F, a x * (ψ_pt x n g : ℂ), ?_, ?_, ?_⟩
  ·
    intro n
    apply continuous_finset_sum
    intro x _
    exact continuous_const.mul (Complex.continuous_ofReal.comp (hcont_pt x n))
  ·
    intro n
    exact hasCompactSupport_finset_sum' fun x _ =>
      ((hsupp_pt x n).comp_left (g := Complex.ofReal) Complex.ofReal_zero).mul_left
  ·
    intro f hf hf_supp
    have key : ∀ x ∈ F, Filter.Tendsto
      (fun n => a x * ∫ g, (ψ_pt x n g : ℂ) * f g)
      Filter.atTop (nhds (a x * f x)) := by
      intro x _
      exact (hconv_pt x f hf hf_supp).const_mul (a x)
    suffices h : ∀ n, ∫ g, (∑ x ∈ F, a x * (ψ_pt x n g : ℂ)) * f g =
      ∑ x ∈ F, a x * ∫ g, (ψ_pt x n g : ℂ) * f g by
      simp_rw [h]
      exact tendsto_finset_sum F (fun x hx => key x hx)
    intro n
    simp_rw [Finset.sum_mul]
    rw [integral_finset_sum]
    · congr 1; ext x
      simp_rw [mul_assoc]
      exact MeasureTheory.integral_const_mul _ _
    · intro x _
      exact ((continuous_const.mul
        (Complex.continuous_ofReal.comp (hcont_pt x n))).mul hf).integrable_of_hasCompactSupport
        hf_supp.mul_left

/--
[simultaneous_diagonal_extraction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma simultaneous_diagonal_extraction
  {F : ℕ → ℕ → ℕ → ℂ}
  {a : ℕ → ℕ → ℂ}
  {b : ℕ → ℂ}
-- given
  (hF : ∀ k n, Filter.Tendsto (F k n) Filter.atTop (nhds (a k n)))
  (ha : ∀ k, Filter.Tendsto (a k) Filter.atTop (nhds (b k))) :
-- imply
  ∃ m : ℕ → ℕ, ∀ k, Filter.Tendsto (fun n => F k n (m n)) Filter.atTop (nhds (b k)) := by
-- proof
  have hmn : ∀ n, ∃ M, ∀ k ≤ n, dist (F k n M) (a k n) < 1 / (↑n + 1) := by
    intro n
    have hε : (0 : ℝ) < 1 / (↑n + 1) := by positivity
    have hconv : ∀ k, ∃ M, ∀ m ≥ M, dist (F k n m) (a k n) < 1 / (↑n + 1) :=
      fun k => (Metric.tendsto_atTop.mp (hF k n)) _ hε
    choose M_k hM_k using hconv
    refine ⟨(Finset.range (n + 1)).sup M_k, fun k hk => ?_⟩
    apply hM_k k
    exact le_trans (Finset.le_sup (f := M_k) (Finset.mem_range.mpr (by omega))) le_rfl
  choose m hm using hmn
  refine ⟨m, fun k => Metric.tendsto_atTop.mpr fun ε hε => ?_⟩
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp (ha k)) (ε / 2) (half_pos hε)
  have h1n : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (↑n + 1)) Filter.atTop (nhds 0) := by
    simp_rw [one_div]
    exact tendsto_inv_atTop_zero.comp
      (Filter.Tendsto.atTop_add (tendsto_natCast_atTop_atTop) tendsto_const_nhds)
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp h1n) (ε / 2) (half_pos hε)
  refine ⟨max (max N₁ N₂) k, fun n hn => ?_⟩
  have hkn : k ≤ n := le_trans (le_max_right _ _) hn
  have step1 : dist (F k n (m n)) (a k n) < 1 / (↑n + 1) := hm n k hkn
  have step3 : 1 / ((↑n : ℝ) + 1) < ε / 2 := by
    have h := hN₂ n (le_trans (le_max_right N₁ N₂) (le_trans (le_max_left _ k) hn))
    simp only [dist_zero_right] at h
    rwa [Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (↑n + 1))] at h
  have step2 : dist (a k n) (b k) < ε / 2 :=
    hN₁ n (le_trans (le_max_left N₁ N₂) (le_trans (le_max_left _ k) hn))
  linarith [dist_triangle (F k n (m n)) (a k n) (b k)]

/--
[smooth_cc_seq_converges_to_dirac](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma smooth_cc_seq_converges_to_dirac
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  [LocallyCompactSpace G]
  [SecondCountableTopology G]
  [MeasureSpace G]
  [BorelSpace G]
  [Measure.IsHaarMeasure (volume : Measure G)]
  [NormedAddCommGroup EG]
  [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG]
  [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG}
  [ChartedSpace HG G]
  [LieGroup IG ⊤ G]
  [T2Space G]
  {g₀ : G} :
-- imply
  ∃ (ψ : ℕ → G → ℝ), (∀ (n : ℕ), ContMDiff IG 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞)) (ψ n)) ∧ (∀ (n : ℕ), HasCompactSupport (ψ n)) ∧ (∀ (f : G → ℂ), Continuous f → HasCompactSupport f → Filter.Tendsto (fun (n : ℕ) => ∫ (g : G), (ψ n g : ℂ) * f g) Filter.atTop (nhds (f g₀))) := by
-- proof
  obtain ⟨φ, hφ_smooth, hφ_supp, hφ_conv⟩ := @exists_smooth_dirac_sequence G _ _ _ _ _ _ _ _ EG _ _ _ HG _ IG _ _ _
  refine ⟨fun n g => φ n (g₀⁻¹ * g), ?_, ?_, ?_⟩
  · intro n
    have hlmul : ContMDiff IG IG (↑(⊤ : ℕ∞)) (fun g : G => g₀⁻¹ * g) := by
      exact contMDiff_const.mul contMDiff_id
    exact (hφ_smooth n).comp hlmul
  · intro n
    exact (hφ_supp n).comp_homeomorph (Homeomorph.mulLeft g₀⁻¹)
  · intro f hf_cont hf_supp
    have key : ∀ n, ∫ g, (φ n (g₀⁻¹ * g) : ℂ) * f g = ∫ h, (φ n h : ℂ) * f (g₀ * h) := by
      intro n
      rw [show (fun g => (φ n (g₀⁻¹ * g) : ℂ) * f g) =
        fun g => ((fun h => (φ n h : ℂ) * f (g₀ * h)) (g₀⁻¹ * g)) from by
        ext g; simp [mul_inv_cancel_left]]
      exact @MeasureTheory.integral_mul_left_eq_self G ℂ _ _ _ (volume) _ _ _
        (fun h => (φ n h : ℂ) * f (g₀ * h)) g₀⁻¹
    simp_rw [key]
    have hfg : Continuous (f ∘ (g₀ * ·)) := hf_cont.comp (continuous_const.mul continuous_id)
    have hfg_supp : HasCompactSupport (f ∘ (g₀ * ·)) :=
      hf_supp.comp_homeomorph (Homeomorph.mulLeft g₀)
    have := hφ_conv (f ∘ (g₀ * ·)) hfg hfg_supp
    simp only [Function.comp, mul_one] at this
    convert this using 1
set_option maxHeartbeats 6400000 in

/--
[kfinite_dense_in_rep](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma kfinite_dense_in_rep
  [Group K]
  [TopologicalSpace K]
  [IsTopologicalGroup K]
  [CompactSpace K]
  [AddCommGroup V]
  [Module ℂ V]
  [TopologicalSpace V]
  {π : ContinuousRep K V} :
-- imply
  Dense (ContinuousRep.kFiniteSubspace π ⊤ : Set V) := by
-- proof
  haveI : CompactSpace (⊤ : Subgroup K) := by
    have : IsCompact ((⊤ : Subgroup K) : Set K) := by
      rwa [Subgroup.coe_top]
    exact isCompact_iff_compactSpace.mp this
  exact ContinuousRep.kFiniteSubspace_dense π ⊤

/--
[matrixCoefficient_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma matrixCoefficient_continuous
  [Group K]
  [TopologicalSpace K]
  [IsTopologicalGroup K]
  [CompactSpace K]
  [AddCommGroup W]
  [Module ℂ W]
  [TopologicalSpace W]
  {ρ : ContinuousRep K W}
  {φ : W →L[ℂ] ℂ}
  {v : W} :
-- imply
  Continuous (ContinuousRep.matrixCoefficient K ρ φ v) := by
-- proof
  unfold ContinuousRep.matrixCoefficient
  exact φ.continuous.comp (ρ.continuous_action.comp (Continuous.prodMk continuous_id continuous_const))

/--
[isKFiniteFunction_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma isKFiniteFunction_continuous
  [Group K]
  [TopologicalSpace K]
  [IsTopologicalGroup K]
  [CompactSpace K]
  {p : K → ℂ}
-- given
  (hp : IsKFiniteFunction K p) :
-- imply
  Continuous p := by
-- proof
  obtain ⟨n, mc, c, hmc, hpg⟩ := hp
  have hmc_cont : ∀ i, Continuous (mc i) := by
    intro i
    obtain ⟨W, hACG, hMod, hTop, hFD, ρ, φ, v, hmci⟩ := hmc i
    rw [hmci]
    exact @matrixCoefficient_continuous K _ _ _ _ W hACG hMod hTop ρ φ v
  have : p = fun g => ∑ i : Fin n, c i * mc i g := funext hpg
  rw [this]
  exact continuous_finset_sum _ (fun i _ => continuous_const.mul (hmc_cont i))

/--
[leftRegularRep_CK_apply_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma leftRegularRep_CK_apply_val
  [Group K]
  [TopologicalSpace K]
  [IsTopologicalGroup K]
  [CompactSpace K]
  {g : K}
  {f : C(K, ℂ)}
  {x : K} :
-- imply
  ((leftRegularRep_CK K).toMonoidHom g f) x = f (g⁻¹ * x) := by
-- proof
  rfl

/--
[leftRegularRep_eval_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma leftRegularRep_eval_identity
  [Group K]
  [TopologicalSpace K]
  [IsTopologicalGroup K]
  [CompactSpace K]
  {f : C(K, ℂ)}
  {g : K} :
-- imply
  f g = ((leftRegularRep_CK K).toMonoidHom g⁻¹ f) (1 : K) := by
-- proof
  simp [leftRegularRep_CK_apply_val, mul_one]

/--
[contragredientFinRep_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma contragredientFinRep_apply
  [AddCommGroup V]
  [Module ℂ V]
  {K : Type*}
  [Group K]
  [TopologicalSpace K]
  [CompactSpace K]
  {ρ : Representation ℂ K V}
  [FiniteDimensional ℂ V]
  {k : K}
  {φ : V →ₗ[ℂ] ℂ}
  {v : V} :
-- imply
  (contragredientFinRep K ρ k φ) v = φ (ρ k⁻¹ v) :=
-- proof
  rfl

/--
[orbit_span_invariant_of_monoidHom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma orbit_span_invariant_of_monoidHom
  [Group G]
  [AddCommGroup V]
  [Module ℂ V]
  [TopologicalSpace V]
  {π : G →* (V →L[ℂ] V)}
  {K : Subgroup G}
  {v : V}
  {g : G}
  {w : V}
-- given
  (hg : g ∈ K)
  (hw : w ∈ Submodule.span ℂ (Set.range (fun k : K => (π k) v))) :
-- imply
  (π g) w ∈ Submodule.span ℂ (Set.range (fun k : K => (π k) v)) := by
-- proof
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨k, hk⟩, rfl⟩ := hx
    have heq : (π g) ((π k) v) = (π (g * k)) v := by
      rw [π.map_mul g k]; rfl
    rw [heq]
    exact Submodule.subset_span ⟨⟨g * k, K.mul_mem hg hk⟩, rfl⟩
  | zero => simp [map_zero]
  | add x y _ _ ihx ihy =>
    rw [map_add]
    exact Submodule.add_mem _ ihx ihy
  | smul c x _ ih =>
    rw [map_smul]
    exact Submodule.smul_mem _ c ih

/--
[kfinite_subspace_dense_in_CK](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma kfinite_subspace_dense_in_CK
  [Group K]
  [TopologicalSpace K]
  [IsTopologicalGroup K]
  [CompactSpace K] :
-- imply
  Dense (ContinuousRep.kFiniteSubspace (leftRegularRep_CK K) ⊤ : Set C(K, ℂ)) :=
-- proof
  kfinite_dense_in_rep (leftRegularRep_CK K)

/--
[irreducible_rep_finiteDimensional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma irreducible_rep_finiteDimensional
  [Group K]
  [TopologicalSpace K]
  [IsTopologicalGroup K]
  [CompactSpace K]
  [AddCommGroup W]
  [Module ℂ W]
  [TopologicalSpace W]
  [IsTopologicalAddGroup W]
  [ContinuousSMul ℂ W]
  [T2Space W]
  {π : ContinuousRep K W}
-- given
  (hirr : π.IsIrreducible) :
-- imply
  FiniteDimensional ℂ W := by
-- proof
  have hdense := kfinite_dense_in_rep π
  by_cases hW : ∀ v : W, v ∈ ContinuousRep.kFiniteSubspace π ⊤ → v = 0
  ·
    have hsub : (ContinuousRep.kFiniteSubspace π ⊤ : Set W) ⊆ {0} := by
      intro v hv; exact hW v hv
    have hdense0 : Dense ({0} : Set W) := Dense.mono hsub hdense
    have hcl : closure ({0} : Set W) = {0} := isClosed_singleton.closure_eq
    have huniv : (Set.univ : Set W) = {0} := by
      rw [← hdense0.closure_eq, hcl]
    have htriv : ∀ w : W, w = 0 := by
      intro w; have hw := Set.mem_univ w; rw [huniv] at hw
      exact Set.mem_singleton_iff.mp hw
    haveI : Subsingleton W := ⟨fun a b => by rw [htriv a, htriv b]⟩
    exact Module.Finite.of_surjective (0 : (Fin 0 → ℂ) →ₗ[ℂ] W)
      (fun w => ⟨0, by simp [htriv w]⟩)
  ·
    push Not at hW
    obtain ⟨v, hv_kfin, hv_ne⟩ := hW
    set S := Submodule.span ℂ (Set.range (fun k : (⊤ : Subgroup K) => (π.toMonoidHom k) v))
      with hS_def
    have hfin : FiniteDimensional ℂ S := by
      have := (ContinuousRep.mem_kFiniteSubspace π ⊤ v).mp hv_kfin
      exact this
    have hinv : ∀ (g : K) (w : W), w ∈ S → (π.toMonoidHom g) w ∈ S := by
      intro g w hw
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
      ·
        intro x hx
        obtain ⟨⟨k, _⟩, rfl⟩ := hx
        have : (π.toMonoidHom g) ((π.toMonoidHom k) v) = (π.toMonoidHom (g * k)) v := by
          simp [map_mul]
        rw [this]
        exact Submodule.subset_span ⟨⟨g * k, Subgroup.mem_top _⟩, rfl⟩
      ·
        simp
      ·
        intro x y _ _ hx' hy'
        rw [map_add]
        exact Submodule.add_mem _ hx' hy'
      ·
        intro c x _ hx'
        rw [map_smul]
        exact Submodule.smul_mem _ c hx'
    have hclosed : IsClosed (S : Set W) := by
      exact Submodule.closed_of_finiteDimensional S
    have hinv_sub : π.IsInvariantSubspace S :=
      ⟨hclosed, hinv⟩
    have h_or := hirr S hinv_sub
    have hv_in_S : v ∈ S := by
      have : v = (π.toMonoidHom 1) v := by simp
      rw [this]
      exact Submodule.subset_span ⟨⟨1, Subgroup.mem_top _⟩, by simp⟩
    have hS_ne_bot : S ≠ ⊥ := by
      intro h
      rw [h] at hv_in_S
      simp at hv_in_S
      exact hv_ne hv_in_S
    have hS_top : S = ⊤ := by
      cases h_or with
      | inl h => exact absurd h hS_ne_bot
      | inr h => exact h
    have : FiniteDimensional ℂ (⊤ : Submodule ℂ W) := hS_top ▸ hfin
    exact Module.Finite.of_surjective (Submodule.subtype (⊤ : Submodule ℂ W))
      (fun w => ⟨⟨w, Submodule.mem_top⟩, rfl⟩)

/--
[derivedRep_preserves_smooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma derivedRep_preserves_smooth
  [Group G]
  [TopologicalSpace G]
  [NormedAddCommGroup EG]
  [NormedSpace ℝ EG]
  [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG}
  [ChartedSpace HG G]
  [LieGroup IG ⊤ G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [CompleteSpace F]
  {π : ContinuousRep G F}
  {lieExp : EG → G}
  {b : EG}
  {v : F}
-- given
  (hExp : ContMDiff 𝓘(ℝ, EG) IG ⊤ lieExp)
  (hExp1 : lieExp 0 = 1)
  (hv : π.IsSmoothVector IG v) :
-- imply
  π.IsSmoothVector IG (π.derivedRep lieExp b v) :=
-- proof
  ContinuousRep.derivedRep_maps_smooth IG π lieExp hExp hExp1 b v hv

/--
[smooth_vectors_dense](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma smooth_vectors_dense
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  [LocallyCompactSpace G]
  [SecondCountableTopology G]
  [MeasureSpace G]
  [BorelSpace G]
  [Measure.IsHaarMeasure (volume : Measure G)]
  [NormedAddCommGroup EG]
  [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG]
  [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG}
  [ChartedSpace HG G]
  [LieGroup IG ⊤ G]
  [T2Space G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [CompleteSpace F]
  {π : ContinuousRep G F} :
-- imply
  Dense (π.smoothSubspace IG : Set F) := by
-- proof
  have hGardDense := ContinuousRep.gardingSubspace_dense IG π
  have hGardLeSmooth : (π.gardingSubspace IG : Set F) ⊆ (π.smoothSubspace IG : Set F) := by
    intro w hw
    have hsub : π.gardingSubspace IG ≤ π.smoothSubspace IG := by
      apply Submodule.span_le.mpr
      intro x ⟨f, v, hf, hx⟩
      rw [hx]
      exact ContinuousRep.gardingVector_isSmooth IG π f hf v
    exact hsub hw
  exact Dense.mono hGardLeSmooth hGardDense

/--
[kfinite_subset_smooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PlancherelCompact.lean)
-/
@[path]
private lemma kfinite_subset_smooth
  [Group G]
  [TopologicalSpace G]
  [NormedAddCommGroup EG]
  [NormedSpace ℝ EG]
  [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG}
  [ChartedSpace HG G]
  [LieGroup IG ⊤ G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [CompleteSpace F]
  {π : ContinuousRep G F}
  {v : F}
-- given
  (hv : ContinuousRep.IsKFinite π ⊤ v) :
-- imply
  π.IsSmoothVector IG v := by
-- proof
  exact ContinuousRep.kfinite_le_smooth IG π hv


-- created on 2026-10-23
-- updated on 2026-10-24
