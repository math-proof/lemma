import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory Filter
open scoped MeasureTheory NNReal ENNReal Topology


namespace TheoryOfProbability3

/--
[ennreal_tendsto_zero_of_squeeze](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/UIConvergenceEquiv.lean)
-/
@[path]
lemma ennreal_tendsto_zero_of_squeeze
  {a b : ℕ → ENNReal}
  {c : ENNReal}
-- given
  (hba : ∀ n, b n ≤ a n)
  (ha : Tendsto a atTop (𝓝 c))
  (hc_ne_top : c ≠ ⊤)
  (h : c ≤ liminf (fun n => a n - b n) atTop) :
-- imply
  Tendsto b atTop (𝓝 0) := by
-- proof
  have hab_tendsto : Tendsto (fun n => a n - b n) atTop (𝓝 c) :=
    tendsto_of_le_liminf_of_limsup_le h
      (limsup_le_limsup (Eventually.of_forall fun _ => tsub_le_self)
        ⟨⊥, fun _ _ => bot_le⟩ ha.isBoundedUnder_le |>.trans ha.limsup_eq.le)
  have ha_ne_top : ∀ᶠ n in atTop, a n ≠ ⊤ :=
    (ha.eventually (gt_mem_nhds (lt_top_iff_ne_top.mpr hc_ne_top))).mono fun _ h => h.ne
  rw [show (0 : ENNReal) = c - c from (tsub_self c).symm]
  exact (ENNReal.Tendsto.sub ha hab_tendsto (.inl hc_ne_top)).congr'
    (ha_ne_top.mono fun n hn => ENNReal.sub_sub_cancel hn (hba n))

end TheoryOfProbability3

namespace TheoryOfProbability3

/--
[scheffe_hn_tendsto_ae](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/UIConvergenceEquiv.lean)
-/
@[path]
lemma scheffe_hn_tendsto_ae
  {m : MeasurableSpace α}
  {μ : Measure α}
  {f : ℕ → α → ℝ}
  {g : α → ℝ}
-- given
  (hae : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
-- imply
  ∀ᵐ x ∂μ, Tendsto (fun n => ‖f n x‖ₑ + ‖g x‖ₑ - ‖f n x - g x‖ₑ) atTop (𝓝 (‖g x‖ₑ + ‖g x‖ₑ)) := by
-- proof
  filter_upwards [hae] with x hx
  have h1 : Tendsto (fun n => ‖f n x‖ₑ) atTop (𝓝 ‖g x‖ₑ) :=
    (continuous_enorm.tendsto _).comp hx
  have h2 : Tendsto (fun n => ‖f n x - g x‖ₑ) atTop (𝓝 0) := by
    have hsub : Tendsto (fun n => f n x - g x) atTop (𝓝 0) := by
      have := hx.sub (@tendsto_const_nhds _ _ _ (g x) _)
      rwa [sub_self] at this
    simpa using (continuous_enorm.tendsto _).comp hsub
  rw [show ‖g x‖ₑ + ‖g x‖ₑ = (‖g x‖ₑ + ‖g x‖ₑ) - 0 from (tsub_zero _).symm]
  exact ENNReal.Tendsto.sub (h1.add tendsto_const_nhds) h2
    (.inl (ENNReal.add_ne_top.mpr ⟨enorm_ne_top, enorm_ne_top⟩))

end TheoryOfProbability3

namespace TheoryOfProbability3

/--
[scheffe_lintegral_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/UIConvergenceEquiv.lean)
-/
@[path]
lemma scheffe_lintegral_eq
  {m : MeasurableSpace α}
  {μ : Measure α}
  {f : ℕ → α → ℝ}
  {g : α → ℝ}
  {n : ℕ}
-- given
  (hfm : ∀ n, AEStronglyMeasurable (f n) μ)
  (hgm : AEStronglyMeasurable g μ)
  (hg : MemLp g 1 μ)
  (hfn : eLpNorm (f n) 1 μ < ⊤) :
-- imply
  ∫⁻ x, (‖f n x‖ₑ + ‖g x‖ₑ - ‖f n x - g x‖ₑ) ∂μ = (eLpNorm (f n) 1 μ + eLpNorm g 1 μ) - eLpNorm (f n - g) 1 μ := by
-- proof
  set ψ : α → ENNReal := fun x => ‖f n x - g x‖ₑ
  have hψ_meas : AEMeasurable ψ μ := ((hfm n).sub hgm).enorm
  have hψ_ne_top : ∫⁻ x, ψ x ∂μ ≠ ⊤ := by
    have : (fun x => ‖f n x - g x‖ₑ) = (fun x => ‖(f n - g) x‖ₑ) := by
      ext; simp [Pi.sub_apply]
    rw [this, ← eLpNorm_one_eq_lintegral_enorm]
    exact ((eLpNorm_sub_le (hfm n) hgm le_rfl).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hfn, hg.eLpNorm_lt_top⟩)).ne
  rw [lintegral_sub' hψ_meas hψ_ne_top (Eventually.of_forall fun x => enorm_sub_le),
    lintegral_add_left' (hfm n).enorm,
    ← eLpNorm_one_eq_lintegral_enorm (f := f n),
    ← eLpNorm_one_eq_lintegral_enorm (f := g)]
  congr 1
  rw [eLpNorm_one_eq_lintegral_enorm]; rfl

end TheoryOfProbability3

namespace TheoryOfProbability3

/--
[scheffe_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/UIConvergenceEquiv.lean)
-/
@[path]
lemma scheffe_lemma
  {m : MeasurableSpace α}
  {μ : Measure α}
  {f : ℕ → α → ℝ}
  {g : α → ℝ}
-- given
  (hfm : ∀ n, AEStronglyMeasurable (f n) μ)
  (hgm : AEStronglyMeasurable g μ)
  (hg : MemLp g 1 μ)
  (hae : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
  (hnorm : Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 (eLpNorm g 1 μ))) :
-- imply
  Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0) := by
-- proof
  set hn : ℕ → α → ENNReal := fun n x => ‖f n x‖ₑ + ‖g x‖ₑ - ‖f n x - g x‖ₑ
  have hn_tendsto_ae := scheffe_hn_tendsto_ae hae
  have C_le : eLpNorm g 1 μ + eLpNorm g 1 μ ≤ ∫⁻ x, liminf (hn · x) atTop ∂μ :=
    (show eLpNorm g 1 μ + eLpNorm g 1 μ = ∫⁻ x, (‖g x‖ₑ + ‖g x‖ₑ) ∂μ by
      rw [eLpNorm_one_eq_lintegral_enorm, lintegral_add_left' hgm.enorm]).symm ▸
    lintegral_mono_ae (hn_tendsto_ae.mono fun x hx => hx.liminf_eq ▸ le_refl _)
  have h_hn_meas : ∀ n, AEMeasurable (hn n) μ := fun n =>
    ((hfm n).enorm.add hgm.enorm).sub ((hfm n).sub hgm).enorm
  have hfn_lt : ∀ᶠ n in atTop, eLpNorm (f n) 1 μ < ⊤ :=
    hnorm.eventually (gt_mem_nhds (lt_top_iff_ne_top.mpr hg.eLpNorm_lt_top.ne))
  have lintegral_hn_eq : ∀ᶠ n in atTop,
    ∫⁻ x, hn n x ∂μ = (eLpNorm (f n) 1 μ + eLpNorm g 1 μ) - eLpNorm (f n - g) 1 μ := by
    filter_upwards [hfn_lt] with n hfn
    exact scheffe_lintegral_eq hfm hgm hg hfn
  have C_le_liminf : eLpNorm g 1 μ + eLpNorm g 1 μ ≤
    liminf (fun n => (eLpNorm (f n) 1 μ + eLpNorm g 1 μ) - eLpNorm (f n - g) 1 μ) atTop :=
    C_le.trans ((lintegral_liminf_le' h_hn_meas).trans (liminf_congr lintegral_hn_eq).le)
  exact ennreal_tendsto_zero_of_squeeze
    (fun n => eLpNorm_sub_le (hfm n) hgm le_rfl)
    (hnorm.add tendsto_const_nhds)
    (ENNReal.add_ne_top.mpr ⟨hg.eLpNorm_lt_top.ne, hg.eLpNorm_lt_top.ne⟩)
    C_le_liminf

end TheoryOfProbability3

namespace TheoryOfProbability3

/--
[tendsto_eLpNorm_of_tendsto_eLpNorm_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/UIConvergenceEquiv.lean)
-/
@[path]
lemma tendsto_eLpNorm_of_tendsto_eLpNorm_sub
  {m : MeasurableSpace α}
  {μ : Measure α}
  {f : ℕ → α → ℝ}
  {g : α → ℝ}
-- given
  (hfm : ∀ n, AEStronglyMeasurable (f n) μ)
  (hgm : AEStronglyMeasurable g μ)
  (hg_ne_top : eLpNorm g 1 μ ≠ ⊤)
  (h : Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0)) :
-- imply
  Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 (eLpNorm g 1 μ)) := by
-- proof
  rw [ENNReal.tendsto_nhds hg_ne_top]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero] at h
  filter_upwards [h ε hε] with n hn
  refine ⟨?_, ?_⟩
  ·
    have h1 : eLpNorm g 1 μ ≤ eLpNorm (f n) 1 μ + ε := by
      calc eLpNorm g 1 μ
        = eLpNorm ((g - f n) + f n) 1 μ := by ring_nf
        _ ≤ eLpNorm (g - f n) 1 μ + eLpNorm (f n) 1 μ :=
          eLpNorm_add_le (hgm.sub (hfm n)) (hfm n) le_rfl
        _ = eLpNorm (f n - g) 1 μ + eLpNorm (f n) 1 μ := by
          rw [show g - f n = -(f n - g) from by ring, eLpNorm_neg]
        _ ≤ ε + eLpNorm (f n) 1 μ := by gcongr
        _ = eLpNorm (f n) 1 μ + ε := add_comm _ _
    exact tsub_le_iff_right.mpr h1
  ·
    calc eLpNorm (f n) 1 μ
      = eLpNorm ((f n - g) + g) 1 μ := by ring_nf
      _ ≤ eLpNorm (f n - g) 1 μ + eLpNorm g 1 μ :=
        eLpNorm_add_le ((hfm n).sub hgm) hgm le_rfl
      _ ≤ ε + eLpNorm g 1 μ := by gcongr
      _ = eLpNorm g 1 μ + ε := add_comm _ _

end TheoryOfProbability3

namespace TheoryOfProbability3

/--
[eLpNorm_uniformly_bounded_of_tendsto_eLpNorm_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/UIConvergenceEquiv.lean)
-/
@[path]
lemma eLpNorm_uniformly_bounded_of_tendsto_eLpNorm_sub
  {m : MeasurableSpace α}
  {μ : Measure α}
  {f : ℕ → α → ℝ}
  {g : α → ℝ}
-- given
  (hf : ∀ n, MemLp (f n) 1 μ)
  (hg : MemLp g 1 μ)
  (hL1 : Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0)) :
-- imply
  ∃ C : NNReal, ∀ i, eLpNorm (f i) 1 μ ≤ C := by
-- proof
  rw [ENNReal.tendsto_nhds_zero] at hL1
  obtain ⟨N, hN⟩ := (hL1 1 one_pos).exists_forall_of_atTop
  have hg_ne : eLpNorm g 1 μ ≠ ⊤ := hg.2.ne
  set Ctail : NNReal := 1 + (eLpNorm g 1 μ).toNNReal
  set Cinit : NNReal := (Finset.range N).sup fun n => (eLpNorm (f n) 1 μ).toNNReal
  refine ⟨Cinit ⊔ Ctail, fun i => ?_⟩
  by_cases hi : i < N
  ·
    have h1 : (eLpNorm (f i) 1 μ).toNNReal ≤ Cinit :=
      Finset.le_sup (f := fun n => (eLpNorm (f n) 1 μ).toNNReal) (Finset.mem_range.mpr hi)
    calc eLpNorm (f i) 1 μ
      = ↑((eLpNorm (f i) 1 μ).toNNReal) := (ENNReal.coe_toNNReal (hf i).2.ne).symm
      _ ≤ ↑Cinit := ENNReal.coe_le_coe.mpr h1
      _ ≤ ↑(Cinit ⊔ Ctail) := ENNReal.coe_le_coe.mpr le_sup_left
  ·
    simp only [not_lt] at hi
    calc eLpNorm (f i) 1 μ
      = eLpNorm ((f i - g) + g) 1 μ := by ring_nf
      _ ≤ eLpNorm (f i - g) 1 μ + eLpNorm g 1 μ :=
        eLpNorm_add_le ((hf i).1.sub hg.1) hg.1 le_rfl
      _ ≤ 1 + eLpNorm g 1 μ := by gcongr; exact hN i hi
      _ = ↑(1 : NNReal) + ↑((eLpNorm g 1 μ).toNNReal) := by
        rw [ENNReal.coe_toNNReal hg_ne, ENNReal.coe_one]
      _ = ↑Ctail := by push_cast; rfl
      _ ≤ ↑(Cinit ⊔ Ctail) := ENNReal.coe_le_coe.mpr le_sup_right

end TheoryOfProbability3

namespace TheoryOfProbability3

/--
[uniformIntegrable_of_tendsto_eLpNorm_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/UIConvergenceEquiv.lean)
-/
@[path]
lemma uniformIntegrable_of_tendsto_eLpNorm_sub
  {m : MeasurableSpace α}
  {μ : Measure α}
  {f : ℕ → α → ℝ}
  {g : α → ℝ}
-- given
  (hf : ∀ n, MemLp (f n) 1 μ)
  (hg : MemLp g 1 μ)
  (hL1 : Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0)) :
-- imply
  UniformIntegrable f 1 μ :=
-- proof
  ⟨fun n => (hf n).1,
    unifIntegrable_of_tendsto_Lp le_rfl ENNReal.one_ne_top hf hg hL1,
    eLpNorm_uniformly_bounded_of_tendsto_eLpNorm_sub hf hg hL1⟩

end TheoryOfProbability3

namespace TheoryOfProbability3

/--
[L1_convergence_imp_norm_convergence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/UIConvergenceEquiv.lean)
-/
@[path]
lemma L1_convergence_imp_norm_convergence
  {m : MeasurableSpace α}
  {μ : Measure α}
  {f : ℕ → α → ℝ}
  {g : α → ℝ}
-- given
  (hfm : ∀ n, AEStronglyMeasurable (f n) μ)
  (hgm : AEStronglyMeasurable g μ)
  (hg : MemLp g 1 μ)
  (hL1 : Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0)) :
-- imply
  Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 (eLpNorm g 1 μ)) ∧ MemLp g 1 μ :=
-- proof
  ⟨tendsto_eLpNorm_of_tendsto_eLpNorm_sub hfm hgm hg.2.ne hL1, hg⟩

end TheoryOfProbability3

namespace TheoryOfProbability3

/--
[norm_convergence_imp_ui](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/UIConvergenceEquiv.lean)
-/
@[path]
lemma norm_convergence_imp_ui
  {m : MeasurableSpace α}
  {μ : Measure α}
  {f : ℕ → α → ℝ}
  {g : α → ℝ}
-- given
  (hf : ∀ n, MemLp (f n) 1 μ)
  (hg : MemLp g 1 μ)
  (hfg : TendstoInMeasure μ f atTop g)
  (hnorm : Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 (eLpNorm g 1 μ))) :
-- imply
  UniformIntegrable f 1 μ := by
-- proof
  have hL1 : Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    have hfg_sub : TendstoInMeasure μ (f ∘ ns) atTop g := fun ε hε => (hfg ε hε).comp hns
    obtain ⟨ms, hms_mono, hms_ae⟩ := hfg_sub.exists_seq_tendsto_ae
    refine ⟨ms, ?_⟩
    exact scheffe_lemma (fun n => (hf (ns (ms n))).1) hg.1 hg hms_ae
      (hnorm.comp (hns.comp hms_mono.tendsto_atTop))
  exact uniformIntegrable_of_tendsto_eLpNorm_sub hf hg hL1
variable [IsFiniteMeasure μ]
  {f : ℕ → α → ℝ} {g : α → ℝ}

end TheoryOfProbability3

namespace TheoryOfProbability3

/--
[ui_imp_L1_convergence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/UIConvergenceEquiv.lean)
-/
@[path]
lemma ui_imp_L1_convergence
  {m : MeasurableSpace α}
  {μ : Measure α}
  [IsFiniteMeasure μ]
-- given
  (hUI : UniformIntegrable f 1 μ)
  (hg : MemLp g 1 μ)
  (hfg : TendstoInMeasure μ f atTop g) :
-- imply
  Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0) :=
-- proof
  tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top hUI.1 hg hUI.2.1 hfg

end TheoryOfProbability3

namespace TheoryOfProbability3

/--
[ui_L1_norm_tfae](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/UIConvergenceEquiv.lean)
-/
@[path]
lemma ui_L1_norm_tfae
  {m : MeasurableSpace α}
  {μ : Measure α}
  [IsFiniteMeasure μ]
-- given
  (hf : ∀ n, MemLp (f n) 1 μ)
  (hg : MemLp g 1 μ)
  (hfg : TendstoInMeasure μ f atTop g) :
-- imply
  [UniformIntegrable f 1 μ, Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0), Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 (eLpNorm g 1 μ))].TFAE := by
-- proof
  tfae_have 1 → 2 := fun h => ui_imp_L1_convergence h hg hfg
  tfae_have 2 → 3 := fun h =>
    (L1_convergence_imp_norm_convergence (fun n => (hf n).1) hg.1 hg h).1
  tfae_have 3 → 1 := fun h => norm_convergence_imp_ui hf hg hfg h
  tfae_finish

end TheoryOfProbability3

namespace TheoryOfProbability3

/--
[uniform_integrability_equivalences](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/UIConvergenceEquiv.lean)
-/
@[path]
lemma uniform_integrability_equivalences
  {m : MeasurableSpace α}
  {μ : Measure α}
  [IsFiniteMeasure μ]
-- given
  (hf : ∀ n, MemLp (f n) 1 μ)
  (hg : MemLp g 1 μ)
  (hfg : TendstoInMeasure μ f atTop g) :
-- imply
  [UniformIntegrable f 1 μ, Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0), Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 (eLpNorm g 1 μ))].TFAE :=
-- proof
  ui_L1_norm_tfae hf hg hfg

end TheoryOfProbability3

/--
[ui_convergence_equivalences](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/UIConvergenceEquiv.lean)
-/
@[path]
lemma ui_convergence_equivalences
  {m : MeasurableSpace α}
  {μ : MeasureTheory.Measure α}
  [MeasureTheory.IsFiniteMeasure μ]
  {f : ℕ → α → ℝ}
  {g : α → ℝ}
-- given
  (hf : ∀ n, MeasureTheory.MemLp (f n) 1 μ)
  (hg : MeasureTheory.MemLp g 1 μ)
  (hfg : MeasureTheory.TendstoInMeasure μ f Filter.atTop g) :
-- imply
  [MeasureTheory.UniformIntegrable f 1 μ, Filter.Tendsto (fun n => MeasureTheory.eLpNorm (f n - g) 1 μ) Filter.atTop (nhds 0), Filter.Tendsto (fun n => MeasureTheory.eLpNorm (f n) 1 μ) Filter.atTop (nhds (MeasureTheory.eLpNorm g 1 μ))].TFAE :=
-- proof
  TheoryOfProbability3.uniform_integrability_equivalences hf hg hfg

/--
[ui_L1_norm_convergence_tfae](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/UIConvergenceEquiv.lean)
-/
@[path]
lemma ui_L1_norm_convergence_tfae
  {m : MeasurableSpace α}
  {μ : MeasureTheory.Measure α}
  [MeasureTheory.IsFiniteMeasure μ]
  {f : ℕ → α → ℝ}
  {g : α → ℝ}
-- given
  (hf : ∀ n, MeasureTheory.MemLp (f n) 1 μ)
  (hg : MeasureTheory.MemLp g 1 μ)
  (hfg : MeasureTheory.TendstoInMeasure μ f Filter.atTop g) :
-- imply
  [MeasureTheory.UniformIntegrable f 1 μ, Filter.Tendsto (fun n => MeasureTheory.eLpNorm (f n - g) 1 μ) Filter.atTop (nhds 0), Filter.Tendsto (fun n => MeasureTheory.eLpNorm (f n) 1 μ) Filter.atTop (nhds (MeasureTheory.eLpNorm g 1 μ))].TFAE :=
-- proof
  TheoryOfProbability3.ui_L1_norm_tfae hf hg hfg


-- created on 2026-10-23
