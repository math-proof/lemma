import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.HeatEquationProp1116
open TemperedDistribution LineDeriv Distribution HeatEquation MeasureTheory in DifferentialOperators
open scoped SchwartzMap


namespace HeatEquation

/--
[isVanishingOn_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquationProp1116.lean)
-/
@[path]
lemma isVanishingOn_sub
  {n : ℕ}
  {u v : 𝓢'(SpaceTime n, ℂ)}
  {s : Set (SpaceTime n)}
-- given
  (hu : IsVanishingOn u s)
  (hv : IsVanishingOn v s) :
-- imply
  IsVanishingOn (u - v) s := by
-- proof
  intro φ hφ
  rw [show (u - v) φ = u φ - v φ from rfl, hu φ hφ, hv φ hφ, sub_self]

end HeatEquation

namespace HeatEquation

/--
[dsupport_sub_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquationProp1116.lean)
-/
@[path]
lemma dsupport_sub_subset
  {n : ℕ}
  {u v : 𝓢'(SpaceTime n, ℂ)} :
-- imply
  dsupport (u - v) ⊆ dsupport u ∪ dsupport v := by
-- proof
  intro x hx
  by_contra h
  simp only [Set.mem_union, not_or] at h
  obtain ⟨hnu, hnv⟩ := h
  simp only [Distribution.notMem_dsupport_iff] at hnu hnv
  obtain ⟨s₁, hvan₁, hopen₁, hx₁⟩ := hnu
  obtain ⟨s₂, hvan₂, hopen₂, hx₂⟩ := hnv
  have hvan : IsVanishingOn (u - v) (s₁ ∩ s₂) :=
    isVanishingOn_sub n (hvan₁.mono Set.inter_subset_left)
      (hvan₂.mono Set.inter_subset_right)
  have : x ∉ dsupport (u - v) := by
    simp only [Distribution.notMem_dsupport_iff]
    exact ⟨s₁ ∩ s₂, hvan, hopen₁.inter hopen₂, ⟨hx₁, hx₂⟩⟩
  exact this hx

end HeatEquation

namespace HeatEquation

/--
[supportedInTimeGeq_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquationProp1116.lean)
-/
@[path]
lemma supportedInTimeGeq_sub
  {n : ℕ}
  {u v : 𝓢'(SpaceTime n, ℂ)}
  {a b : ℝ}
-- given
  (ha : SupportedInTimeGeq n u a)
  (hb : SupportedInTimeGeq n v b) :
-- imply
  SupportedInTimeGeq n (u - v) (min a b) := by
-- proof
  intro x hx
  have hsub := dsupport_sub_subset n u v hx
  simp only [Set.mem_union] at hsub
  simp only [Set.mem_setOf_eq]
  obtain hu | hv := hsub
  · exact le_trans (min_le_left a b) (ha hu)
  · exact le_trans (min_le_right a b) (hb hv)

end HeatEquation

namespace HeatEquation

/--
[supportedInTimeGeq_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquationProp1116.lean)
-/
@[path]
lemma supportedInTimeGeq_neg
  {n : ℕ}
  {u : 𝓢'(SpaceTime n, ℂ)}
  {c : ℝ} :
-- imply
  SupportedInTimeGeq n (-u) c ↔ SupportedInTimeGeq n u c := by
-- proof
  unfold SupportedInTimeGeq
  constructor
  · intro h x hx
    apply h
    rw [Distribution.mem_dsupport_iff] at hx ⊢
    intro C hvan hclosed
    apply hx C _ hclosed
    intro φ hφ
    have := hvan φ hφ
    show u φ = 0
    rwa [show (-u) φ = -(u φ) from rfl, neg_eq_zero] at this
  · intro h x hx
    apply h
    rw [Distribution.mem_dsupport_iff] at hx ⊢
    intro C hvan hclosed
    apply hx C _ hclosed
    intro φ hφ
    have := hvan φ hφ
    show -(u φ) = 0
    rw [this, neg_zero]

end HeatEquation

namespace HeatEquation

/--
[compact_dsupport_time_bounded_below](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquationProp1116.lean)
-/
@[path]
lemma compact_dsupport_time_bounded_below
  {n : ℕ}
  {f : 𝓢'(SpaceTime n, ℂ)}
-- given
  (hf : HasCompactDSupport n f) :
-- imply
  ∃ b : ℝ, SupportedInTimeGeq n f b := by
-- proof
  by_cases hempty : dsupport f = ∅
  · exact ⟨0, fun x hx => (hempty ▸ hx : x ∈ (∅ : Set _)).elim⟩
  · have hne : Set.Nonempty (dsupport f) := Set.nonempty_iff_ne_empty.mpr hempty
    have hcont : Continuous (timeCoord n) :=
      PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) 0
    obtain ⟨x₀, _, hx₀_min⟩ := hf.exists_isMinOn hne hcont.continuousOn
    exact ⟨timeCoord n x₀, fun x hx => hx₀_min hx⟩

end HeatEquation

namespace HeatEquation

/--
[heatKernelFun_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquationProp1116.lean)
-/
@[path]
lemma heatKernelFun_nonneg
  {n : ℕ}
  {v : SpaceTime n} :
-- imply
  0 ≤ heatKernelFun n v := by
-- proof
  simp only [heatKernelFun]
  split_ifs with ht
  · apply mul_nonneg
    · exact Real.rpow_nonneg (mul_nonneg (mul_nonneg (by positivity) Real.pi_pos.le) ht.le) _
    · exact (Real.exp_pos _).le
  · exact le_rfl

end HeatEquation

namespace HeatEquation

/--
[heatKernelFun_eq_zero_of_time_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquationProp1116.lean)
-/
@[path]
lemma heatKernelFun_eq_zero_of_time_nonpos
  {n : ℕ}
  {v : SpaceTime n}
-- given
  (hv : v (0 : Fin (n + 1)) ≤ 0) :
-- imply
  heatKernelFun n v = 0 := by
-- proof
  simp only [heatKernelFun]
  split_ifs with ht
  · linarith
  · rfl

end HeatEquation

namespace HeatEquation

/--
[heatKernelMeasure_nonpos_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquationProp1116.lean)
-/
@[path]
lemma heatKernelMeasure_nonpos_eq_zero
  {n : ℕ} :
-- imply
  (heatKernelMeasure n) {v : SpaceTime n | v 0 ≤ 0} = 0 := by
-- proof
  have hms : MeasurableSet {v : SpaceTime n | v 0 ≤ 0} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  rw [heatKernelMeasure, withDensity_apply _ hms]
  exact setLIntegral_eq_zero hms (fun v (hv : v 0 ≤ 0) => by
    simp only [Pi.zero_apply]
    rw [heatKernelFun_eq_zero_of_time_nonpos n v hv, ENNReal.ofReal_zero])

end HeatEquation

namespace HeatEquation

/--
[heatKernelFun_le_one_of_time_ge_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquationProp1116.lean)
-/
@[path]
lemma heatKernelFun_le_one_of_time_ge_one
  {n : ℕ}
  {v : SpaceTime n}
-- given
  (ht : v (0 : Fin (n+1)) ≥ 1) :
-- imply
  heatKernelFun n v ≤ 1 := by
-- proof
  simp only [heatKernelFun]
  split_ifs with h
  · exact le_trans (mul_le_one₀
    (Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [Real.pi_gt_three])
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith))
    (Real.exp_pos _).le
    (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg _)) (by positivity)))) le_rfl
  · linarith
open MeasureTheory in
set_option maxHeartbeats 800000 in

end HeatEquation

namespace HeatEquation

/--
[heatKernelMeasure_le_volume_on_time_ge_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquationProp1116.lean)
-/
@[path]
lemma heatKernelMeasure_le_volume_on_time_ge_one
  {n : ℕ} :
-- imply
  (heatKernelMeasure n).restrict {v : SpaceTime n | v (0 : Fin (n+1)) ≥ 1} ≤ MeasureTheory.volume.restrict {v : SpaceTime n | v (0 : Fin (n+1)) ≥ 1} := by
-- proof
  rw [MeasureTheory.Measure.le_iff]
  intro A hA
  rw [MeasureTheory.Measure.restrict_apply hA, MeasureTheory.Measure.restrict_apply hA]
  have hms : MeasurableSet (A ∩ {v : SpaceTime n | v (0 : Fin (n+1)) ≥ 1}) :=
    hA.inter (measurableSet_le (by fun_prop) (by fun_prop))
  rw [heatKernelMeasure, MeasureTheory.withDensity_apply _ hms]
  calc ∫⁻ v in A ∩ {v | v (0 : Fin (n+1)) ≥ 1},
    ENNReal.ofReal (heatKernelFun n v) ∂MeasureTheory.volume
    ≤ ∫⁻ _ in A ∩ {v | v (0 : Fin (n+1)) ≥ 1}, 1 ∂MeasureTheory.volume := by
      apply MeasureTheory.setLIntegral_mono (by fun_prop)
      intro v hv
      have hvS : v (0 : Fin (n+1)) ≥ 1 := hv.2
      exact ENNReal.ofReal_le_one.mpr
        (heatKernelFun_le_one_of_time_ge_one n v hvS)
    _ = MeasureTheory.volume (A ∩ {v | v (0 : Fin (n+1)) ≥ 1}) := by simp

end HeatEquation

/--
[HeatEquation.integrable_rexp_neg_mul_sq_norm_euclidean](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquationProp1116.lean)
-/
@[path]
lemma HeatEquation.integrable_rexp_neg_mul_sq_norm_euclidean
  {m : ℕ}
  {b : ℝ}
-- given
  (hb : 0 < b) :
-- imply
  MeasureTheory.Integrable (fun v : EuclideanSpace ℝ (Fin m) => Real.exp (-b * ‖v‖ ^ 2)) MeasureTheory.volume := by
-- proof
  have hcint := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (show (0 : ℝ) < (↑b : ℂ).re by simp [hb]) (0 : ℂ) (0 : EuclideanSpace ℝ (Fin m))
  simp only [zero_mul, add_zero] at hcint
  refine hcint.re.congr (MeasureTheory.ae_of_all _ fun v => ?_)
  simp only
  have h1 : (-↑b * ↑‖v‖ ^ 2 : ℂ) = ↑(-b * ‖v‖ ^ 2) := by push_cast; ring
  rw [h1]; exact Complex.ofReal_re _

/--
[HeatEquation.heatKernelFun_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquationProp1116.lean)
-/
@[path]
lemma HeatEquation.heatKernelFun_measurable
  {n : ℕ} :
-- imply
  Measurable (heatKernelFun n) := by
-- proof
  unfold heatKernelFun
  apply Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
  · exact (by fun_prop : Measurable _).mul (by fun_prop)
  · exact measurable_const

/--
[HeatEquation.forwardFundSol_support](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquationProp1116.lean)
-/
@[path]
lemma HeatEquation.forwardFundSol_support
  {n : ℕ} :
-- imply
  SupportedInTimeGeq n (forwardFundSol n) 0 := by
-- proof
  intro x hx
  simp only [Set.mem_setOf_eq]
  by_contra hlt
  push Not at hlt
  rw [mem_dsupport_iff_not_isVanishingOn] at hx
  have hopen : IsOpen {v : SpaceTime n | timeCoord n v < 0} :=
    isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) 0) continuous_const
  have := hx _ hlt hopen
  apply this
  intro φ hφ
  simp only [forwardFundSol, MeasureTheory.Measure.toTemperedDistribution_apply]
  apply integral_eq_zero_of_ae
  rw [Filter.EventuallyEq, ae_iff]
  apply measure_mono_null _ (heatKernelMeasure_nonpos_eq_zero n)
  intro v hv
  simp only [Set.mem_setOf_eq, Pi.zero_apply] at hv ⊢
  have hmem : v ∈ Function.support (⇑φ) := hv
  have htsup : v ∈ tsupport (⇑φ) := subset_tsupport _ hmem
  have hlt2 := hφ htsup
  simp only [Set.mem_setOf_eq, timeCoord] at hlt2
  exact le_of_lt hlt2

/--
[HeatEquation.reflConvSchwartzMap_apply_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquationProp1116.lean)
-/
@[path]
lemma HeatEquation.reflConvSchwartzMap_apply_zero
  {n : ℕ}
  {f : 𝓢'(SpaceTime n, ℂ)}
  {φ : 𝓢(SpaceTime n, ℂ)}
-- given
  (hf : HasCompactDSupport n f) :
-- imply
  (reflConvSchwartzMap n f hf φ) 0 = f φ := by
-- proof
  simp only [reflConvSchwartzMap, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
    compactDsupportConvolutionSchwartzMap_apply, SchwartzMap.compSubConstCLM_zero,
    ContinuousLinearMap.id_apply]

/--
[HeatEquation.compactDsupport_conv_fderiv_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquationProp1116.lean)
-/
@[path]
lemma HeatEquation.compactDsupport_conv_fderiv_eq
  {n : ℕ}
  {f : 𝓢'(SpaceTime n, ℂ)}
  {m : SpaceTime n}
  {φ : 𝓢(SpaceTime n, ℂ)}
  {x : SpaceTime n}
-- given
  (hf : HasCompactDSupport n f) :
-- imply
  (fderiv ℝ (⇑(compactDsupportConvolutionSchwartzMap f hf φ)) x) m = f ((SchwartzMap.compSubConstCLM ℂ x) (∂_{-m} φ)) := by
-- proof
  have hfun_eq : (⇑(compactDsupportConvolutionSchwartzMap f hf φ) : SpaceTime n → ℂ) =
    (fun z => f (SchwartzMap.compSubConstCLM ℂ z φ)) := by ext z; rfl
  rw [hfun_eq]
  exact SmoothingOperators.schwartz_translation_fderiv_apply f φ x m

/--
[HeatEquation.reflConvSchwartzMap_comm_lineDerivOp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquationProp1116.lean)
-/
@[path]
lemma HeatEquation.reflConvSchwartzMap_comm_lineDerivOp
  {n : ℕ}
  {f : 𝓢'(SpaceTime n, ℂ)}
  {m : SpaceTime n}
  {φ : 𝓢(SpaceTime n, ℂ)}
-- given
  (hf : HasCompactDSupport n f) :
-- imply
  reflConvSchwartzMap n f hf (∂_{-m} φ) = ∂_{m} (reflConvSchwartzMap n f hf φ) := by
-- proof
  ext x
  simp only [reflConvSchwartzMap, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
    compactDsupportConvolutionSchwartzMap_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  exact (compactDsupport_conv_fderiv_eq n f hf m φ x).symm

/--
[HeatEquation.lineDerivOp_dconv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquationProp1116.lean)
-/
@[path]
lemma HeatEquation.lineDerivOp_dconv
  {n : ℕ}
  {u f : 𝓢'(SpaceTime n, ℂ)}
  {m : SpaceTime n}
-- given
  (hf : HasCompactDSupport n f) :
-- imply
  ∂_{-m} (dconv n u f hf) = dconv n (∂_{m} u) f hf := by
-- proof
  ext φ
  change u (reflConvSchwartzMap n f hf (-∂_{-m} φ)) = (∂_{m} u) (reflConvSchwartzMap n f hf φ)
  rw [show -∂_{-m} φ = ∂_{m} φ from by ext y; simp [SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.neg_apply, map_neg]]
  have hcomm := reflConvSchwartzMap_comm_lineDerivOp n f hf m φ
  have hcomm' : reflConvSchwartzMap n f hf (∂_{m} φ) = ∂_{-m} (reflConvSchwartzMap n f hf φ) := by
    have := reflConvSchwartzMap_comm_lineDerivOp n f hf (-m) φ
    simp only [neg_neg] at this
    exact this
  rw [hcomm']
  rw [lineDerivOp_apply_apply]
  congr 1
  ext y
  simp [SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.neg_apply, map_neg]

/--
[HeatEquation.delta_dconv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquationProp1116.lean)
-/
@[path]
lemma HeatEquation.delta_dconv
  {n : ℕ}
  {f : 𝓢'(SpaceTime n, ℂ)}
-- given
  (hf : HasCompactDSupport n f) :
-- imply
  dconv n (delta 0) f hf = f := by
-- proof
  ext φ
  simp only [dconv]
  show (delta (0 : SpaceTime n)) (reflConvSchwartzMap n f hf φ) = f φ
  rw [TemperedDistribution.delta_apply]
  exact reflConvSchwartzMap_apply_zero n f hf φ
open HeatEquation in
set_option maxHeartbeats 800000 in

/--
[HeatEquation.isVanishingOn_compl_of_dsupport_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquationProp1116.lean)
-/
@[path]
lemma HeatEquation.isVanishingOn_compl_of_dsupport_subset
  {n : ℕ}
  {u : 𝓢'(SpaceTime n, ℂ)}
  {S : Set (SpaceTime n)}
-- given
  (hS : IsClosed S)
  (h : dsupport u ⊆ S) :
-- imply
  IsVanishingOn u Sᶜ := by
-- proof
  intro φ hφ
  suffices h_compact : ∀ (ψ : 𝓢(SpaceTime n, ℂ)),
    HasCompactSupport ψ → tsupport (⇑ψ) ⊆ Sᶜ → u ψ = 0 by
    have htend : Filter.Tendsto (fun m => SchwartzMap.bumpCutoffMul m φ)
      Filter.atTop (nhds φ) := by
      rw [(schwartz_withSeminorms ℂ (SpaceTime n) ℂ).tendsto_nhds _ φ]
      intro ⟨k, j⟩ ε hε
      have h1 := SchwartzMap.seminorm_cutoff_sub_tendsto ℂ φ k j
      rw [Metric.tendsto_atTop] at h1
      obtain ⟨N, hN⟩ := h1 ε hε
      filter_upwards [Filter.Ici_mem_atTop N] with m hm
      simp only [SchwartzMap.schwartzSeminormFamily_apply]
      have h2 := hN m hm
      rw [Real.dist_0_eq_abs, abs_of_nonneg (apply_nonneg _ _)] at h2
      calc (SchwartzMap.seminorm ℂ k j) (SchwartzMap.bumpCutoffMul m φ - φ)
        = (SchwartzMap.seminorm ℂ k j) (φ - SchwartzMap.bumpCutoffMul m φ) := by
          rw [← map_neg_eq_map]; congr 1; abel
        _ < ε := h2
    have hvanish : ∀ m : ℕ, u (SchwartzMap.bumpCutoffMul m φ) = 0 := by
      intro m
      apply h_compact
      · exact SchwartzMap.bumpCutoffMul_hasCompactSupport m φ
      · calc tsupport ⇑(SchwartzMap.bumpCutoffMul m φ)
        ⊆ tsupport (⇑φ) := by
          apply closure_mono; intro x hx
          rw [Function.mem_support] at hx ⊢
          intro hf; apply hx; simp [hf]
        _ ⊆ Sᶜ := hφ
    have hclosed : IsClosed {ψ : 𝓢(SpaceTime n, ℂ) | u ψ = 0} :=
      isClosed_eq u.cont continuous_const
    have hmem : φ ∈ closure {ψ : 𝓢(SpaceTime n, ℂ) | u ψ = 0} := by
      apply mem_closure_of_tendsto htend
      exact Filter.Eventually.of_forall hvanish
    have hmem2 : φ ∈ {ψ : 𝓢(SpaceTime n, ℂ) | u ψ = 0} :=
      closure_minimal (fun ψ hψ => hψ) hclosed hmem
    exact hmem2
  intro ψ hcs hψ
  classical
  have h_Sc_vanish : ∀ x ∈ Sᶜ, ∃ V : Set (SpaceTime n),
    IsOpen V ∧ x ∈ V ∧ IsVanishingOn u V := by
    intro x hx
    have : x ∉ dsupport u := fun hd => hx (h hd)
    rw [notMem_dsupport_iff] at this
    obtain ⟨V, hV_van, hV_open, hx_mem⟩ := this
    exact ⟨V, hV_open, hx_mem, hV_van⟩
  let V : SpaceTime n → Set (SpaceTime n) := fun x =>
    if hx : x ∈ Sᶜ then (h_Sc_vanish x hx).choose else (tsupport (⇑ψ))ᶜ
  have hV_open : ∀ x, IsOpen (V x) := by
    intro x; simp only [V]
    split_ifs with hx
    · exact (h_Sc_vanish x hx).choose_spec.1
    · exact (isClosed_tsupport _).isOpen_compl
  have hV_mem : ∀ x, x ∈ V x := by
    intro x; simp only [V]
    split_ifs with hx
    · exact (h_Sc_vanish x hx).choose_spec.2.1
    · exact fun hmem => hx (hψ hmem)
  have hV_cover : Set.univ ⊆ ⋃ x, V x :=
    fun x _ => Set.mem_iUnion.mpr ⟨x, hV_mem x⟩
  obtain ⟨ρ, hρ_sub⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (SpaceTime n)) isClosed_univ V hV_open hV_cover
  have hlf := ρ.locallyFinite
  have hfin : {i | (Function.support (⇑(ρ i)) ∩ tsupport (⇑ψ)).Nonempty}.Finite :=
    hlf.finite_nonempty_inter_compact hcs
  set s := hfin.toFinset with hs_def
  have hρ_smooth : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (ρ i : SpaceTime n → ℝ) := by
    intro i; rw [← contMDiff_iff_contDiff]; exact (ρ i).contMDiff
  have hprod_cs : ∀ i, HasCompactSupport (fun x => (↑(ρ i x) : ℂ) * ψ x) :=
    fun i => hcs.mul_left
  have hprod_smooth : ∀ i,
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (↑(ρ i x) : ℂ) * ψ x) :=
    fun i => (Complex.ofRealCLM.contDiff.comp (hρ_smooth i)).mul (ψ.smooth ⊤)
  let g : SpaceTime n → 𝓢(SpaceTime n, ℂ) :=
    fun i => (hprod_cs i).toSchwartzMap (hprod_smooth i)
  have hg_vanish : ∀ i, u (g i) = 0 := by
    intro i
    by_cases hi : i ∈ Sᶜ
    · have hV_van : IsVanishingOn u (V i) := by
      simp only [V, dif_pos hi]
      exact (h_Sc_vanish i hi).choose_spec.2.2
      have hg_tsup : tsupport (⇑(g i)) ⊆ V i := by
        calc tsupport ⇑(g i) ⊆ tsupport (ρ i : SpaceTime n → ℝ) := by
          apply closure_mono; intro x hx
          rw [Function.mem_support] at hx ⊢
          intro hρx; apply hx
          show (↑(ρ i x) : ℂ) * ψ x = 0; simp [hρx]
          _ ⊆ V i := hρ_sub i
      exact hV_van _ hg_tsup
    · have hV_eq : V i = (tsupport (⇑ψ))ᶜ := by simp only [V]; rw [dif_neg hi]
      have hgi_zero : g i = 0 := by
        ext x; show (↑(ρ i x) : ℂ) * ψ x = 0
        by_cases hρ : (ρ i) x = 0
        · simp [hρ]
        · have hx_in_V : x ∈ V i :=
          (hρ_sub i) (subset_tsupport _ (Function.mem_support.mpr hρ))
          rw [hV_eq] at hx_in_V
          simp [image_eq_zero_of_notMem_tsupport hx_in_V]
      rw [hgi_zero, map_zero]
  have hψ_eq : ψ = ∑ i ∈ s, g i := by
    ext x
    have hsum_app : (∑ i ∈ s, g i) x = ∑ i ∈ s, (g i) x := by simp
    rw [hsum_app]
    have heq : ∀ i, (g i) x = (↑(ρ i x) : ℂ) * ψ x :=
      fun i => (hprod_cs i).toSchwartzMap_toFun (hprod_smooth i) x
    simp_rw [heq, ← Finset.sum_mul]
    by_cases hψx : (ψ : SpaceTime n → ℂ) x = 0
    · simp [hψx]
    · have hx_supp : x ∈ tsupport (⇑ψ) :=
      subset_tsupport _ (Function.mem_support.mpr hψx)
      have hρ_zero : ∀ i, i ∉ s → (ρ i) x = 0 := by
        intro i hi; by_contra h'
        exact hi (hs_def ▸ hfin.mem_toFinset.mpr
          ⟨x, Function.mem_support.mpr h', hx_supp⟩)
      have hsum_one : ∑ᶠ i, (ρ i) x = 1 := ρ.sum_eq_one (Set.mem_univ x)
      have hsupp : Function.support (fun i => (ρ i) x) ⊆ ↑s := by
        intro i hi; rw [Finset.mem_coe]
        by_contra hi'; exact (Function.mem_support.mp hi) (hρ_zero i hi')
      rw [finsum_eq_sum_of_support_subset _ hsupp] at hsum_one
      have hcsum : (∑ i ∈ s, (↑(ρ i x) : ℂ)) = 1 := by
        rw [← Complex.ofReal_one, ← hsum_one]; push_cast; rfl
      rw [hcsum, one_mul]
  rw [hψ_eq, map_sum]
  exact Finset.sum_eq_zero (fun i _ => hg_vanish i)
open HeatEquation in
/-- Support property of the reflected-convolution Schwartz map: if `f` is supported in
`{t ≥ b}` and `φ` has time support in `{t < a + b}`, then the convolution
`reflConvSchwartzMap n f hf φ` has time support in `{t < a}`. -/
namespace HeatEquation
variable (n : ℕ)

namespace HeatEquation

/--
[heatOperator_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquationProp1116.lean)
-/
@[path]
lemma heatOperator_sub
  {n : ℕ}
  {u v : 𝓢'(SpaceTime n, ℂ)} :
-- imply
  heatOperator n (u - v) = heatOperator n u - heatOperator n v := by
-- proof
  simp only [heatOperator, positiveSpatialLaplacian, sub_eq_add_neg,
    lineDerivOp_add, lineDerivOp_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  abel
/-- Proposition 11.16 (existence and uniqueness for the heat equation): for every tempered
distribution `f` with compact distributional support, there is a unique tempered distribution `u`,
bounded below in time, satisfying `(∂_t - Δ_x) u = f`. -/
end HeatEquation
end



-- created on 2026-10-23
