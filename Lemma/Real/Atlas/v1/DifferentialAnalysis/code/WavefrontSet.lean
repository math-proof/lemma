import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.DifferentialAnalysis.code.WavefrontSet.Part3
open MeasureTheory Set ConeSupport WavefrontSet
open scoped SchwartzMap FourierTransform
open scoped Topology
open Set
open scoped SchwartzMap


namespace ConeSupport

/--
[isCompactlySupportedDistribution_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma isCompactlySupportedDistribution_sub
  {n : ℕ}
  {u₁ u₂ : 𝓢'(E n, ℂ)}
-- given
  (h₁ : IsCompactlySupportedDistribution u₁)
  (h₂ : IsCompactlySupportedDistribution u₂) :
-- imply
  IsCompactlySupportedDistribution (u₁ - u₂) := by
-- proof
  obtain ⟨K₁, hK₁_compact, hK₁_vanish⟩ := h₁
  obtain ⟨K₂, hK₂_compact, hK₂_vanish⟩ := h₂
  refine ⟨K₁ ∪ K₂, hK₁_compact.union hK₂_compact, fun f hf => ?_⟩
  have hf₁ : Function.support (⇑f) ∩ K₁ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have := Set.eq_empty_iff_forall_notMem.mp hf x
    exact this (Set.mem_inter hx.1 (Set.mem_union_left K₂ hx.2))
  have hf₂ : Function.support (⇑f) ∩ K₂ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have := Set.eq_empty_iff_forall_notMem.mp hf x
    exact this (Set.mem_inter hx.1 (Set.mem_union_right K₁ hx.2))
  simp only [UniformConvergenceCLM.sub_apply, hK₁_vanish f hf₁, hK₂_vanish f hf₂, sub_zero]

end ConeSupport

namespace ConeSupport

/--
[isCompactlySupportedDistribution_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma isCompactlySupportedDistribution_add
  {n : ℕ}
  {u₁ u₂ : 𝓢'(E n, ℂ)}
-- given
  (h₁ : IsCompactlySupportedDistribution u₁)
  (h₂ : IsCompactlySupportedDistribution u₂) :
-- imply
  IsCompactlySupportedDistribution (u₁ + u₂) := by
-- proof
  obtain ⟨K₁, hK₁_compact, hK₁_vanish⟩ := h₁
  obtain ⟨K₂, hK₂_compact, hK₂_vanish⟩ := h₂
  refine ⟨K₁ ∪ K₂, hK₁_compact.union hK₂_compact, fun f hf => ?_⟩
  have hf₁ : Function.support (⇑f) ∩ K₁ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have := Set.eq_empty_iff_forall_notMem.mp hf x
    exact this (Set.mem_inter hx.1 (Set.mem_union_left K₂ hx.2))
  have hf₂ : Function.support (⇑f) ∩ K₂ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have := Set.eq_empty_iff_forall_notMem.mp hf x
    exact this (Set.mem_inter hx.1 (Set.mem_union_right K₁ hx.2))
  simp only [UniformConvergenceCLM.add_apply, hK₁_vanish f hf₁, hK₂_vanish f hf₂, add_zero]

end ConeSupport

namespace ConeSupport

/--
[isCompactlySupportedDistribution_of_supported_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma isCompactlySupportedDistribution_of_supported_at_zero
  {n : ℕ}
  {u : 𝓢'(E n, ℂ)}
-- given
  (h : ∀ f : 𝓢(E n, ℂ), (∀ x : E n, f x ≠ 0 → x ≠ 0) → u f = 0) :
-- imply
  IsCompactlySupportedDistribution u := by
-- proof
  refine ⟨{0}, isCompact_singleton, fun f hf => ?_⟩
  apply h
  intro x hfx hx_eq
  have hmem : x ∈ Function.support (⇑f) ∩ ({(0 : E n)} : Set (E n)) :=
    Set.mem_inter (Function.mem_support.mpr hfx) (by rw [hx_eq]; exact Set.mem_singleton _)
  rwa [hf] at hmem

end ConeSupport

namespace ConeSupport

/--
[schwDistribConv_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma schwDistribConv_add
  {n : ℕ}
  {v : 𝓢'(E n, ℂ)}
  {φ₁ φ₂ : 𝓢(E n, ℂ)} :
-- imply
  schwDistribConv v (φ₁ + φ₂) = schwDistribConv v φ₁ + schwDistribConv v φ₂ := by
-- proof
  unfold schwDistribConv schwartzConvolution
  have href : schwartzReflectionCLM (φ₁ + φ₂) =
    (schwartzReflectionCLM φ₁ + schwartzReflectionCLM φ₂ : 𝓢(E n, ℂ)) := map_add _ _ _
  rw [href, map_add]
  ext ψ
  exact map_add v _ _

end ConeSupport

namespace ConeSupport

/--
[convolution_decomp_well_defined](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma convolution_decomp_well_defined
  {n : ℕ}
  {u : 𝓢'(E n, ℂ)}
  {C : ConvolutionSystem n}
  {d₁ d₂ : SchwartzCompactDecomp u}
-- given
  (hu : HasEmptyConicSingularSupportSphere u) :
-- imply
  C.convSchwartz d₁.schwartzPart + C.convCompact d₁.compactPart = C.convSchwartz d₂.schwartzPart + C.convCompact d₂.compactPart := by
-- proof
  set f₁ := d₁.schwartzPart
  set f₂ := d₂.schwartzPart
  set g₁ := d₁.compactPart
  set g₂ := d₂.compactPart
  have hdecomp : schwEmbed f₁ + g₁ = schwEmbed f₂ + g₂ := by
    rw [← d₁.sum_eq, ← d₂.sum_eq]
  have hg₂ : g₂ = schwEmbed (f₁ - f₂) + g₁ := by
    have h : schwEmbed f₁ + g₁ - schwEmbed f₂ = g₂ := by rw [hdecomp]; abel
    show g₂ = schwEmbed (f₁ - f₂) + g₁
    rw [map_sub, ← h]; abel
  have hw : IsCompactlySupportedDistribution (schwEmbed (f₁ - f₂)) := by
    rw [map_sub]; exact hu.diff_compactlySupported d₁ d₂
  have step1 : C.convSchwartz f₁ = C.convSchwartz f₂ + C.convSchwartz (f₁ - f₂) := by
    have h := C.convSchwartz_add f₂ (f₁ - f₂)
    simp only [add_sub_cancel] at h
    exact h
  have step2 : C.convSchwartz (f₁ - f₂) = C.convCompact (schwEmbed (f₁ - f₂)) :=
    C.convSchwartz_eq_compact _ hw
  have step3 : C.convCompact g₂ =
    C.convCompact (schwEmbed (f₁ - f₂)) + C.convCompact g₁ := by
    rw [hg₂, C.convCompact_add]
  calc C.convSchwartz f₁ + C.convCompact g₁
    = (C.convSchwartz f₂ + C.convSchwartz (f₁ - f₂)) + C.convCompact g₁ := by rw [step1]
    _ = (C.convSchwartz f₂ + C.convCompact (schwEmbed (f₁ - f₂))) + C.convCompact g₁ := by
      rw [step2]
    _ = C.convSchwartz f₂ + (C.convCompact (schwEmbed (f₁ - f₂)) + C.convCompact g₁) := by
      rw [add_assoc]
    _ = C.convSchwartz f₂ + C.convCompact g₂ := by rw [← step3]

end ConeSupport

namespace ConeSupport

/--
[sphereNeg_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma sphereNeg_val
  {n : ℕ}
  {ω : Sphere n} :
-- imply
  (sphereNeg ω).1 = -ω.1 :=
-- proof
  rfl

end ConeSupport

namespace ConeSupport

/--
[sphereNeg_sphereNeg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma sphereNeg_sphereNeg
  {n : ℕ}
  {ω : Sphere n} :
-- imply
  sphereNeg (sphereNeg ω) = ω := by
-- proof
  apply Subtype.ext
  simp only [sphereNeg_val, neg_neg]

end ConeSupport

namespace ConeSupport

/--
[mem_negSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma mem_negSet_iff
  {n : ℕ}
  {S : Set (Sphere n)}
  {ω : Sphere n} :
-- imply
  ω ∈ negSet S ↔ sphereNeg ω ∈ S := by
-- proof
  constructor
  · rintro ⟨ω', hω', rfl⟩
    rwa [sphereNeg_sphereNeg]
  · intro h
    exact ⟨sphereNeg ω, h, sphereNeg_sphereNeg ω⟩

end ConeSupport

namespace ConeSupport

/--
[neg_hasTemperateGrowth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma neg_hasTemperateGrowth
  {n : ℕ} :
-- imply
  Function.HasTemperateGrowth (Neg.neg : E n → E n) :=
-- proof
  (ContinuousLinearEquiv.neg ℝ : E n ≃L[ℝ] E n).toContinuousLinearMap.hasTemperateGrowth

end ConeSupport

namespace ConeSupport

/--
[hasTemperateGrowth_comp_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma hasTemperateGrowth_comp_neg
  {n : ℕ}
  {g : E n → ℂ}
-- given
  (hg : Function.HasTemperateGrowth g) :
-- imply
  Function.HasTemperateGrowth (g ∘ Neg.neg) :=
-- proof
  hg.comp neg_hasTemperateGrowth

end ConeSupport

namespace ConeSupport

/--
[hasTemperateGrowth_neg_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma hasTemperateGrowth_neg_iff
  {n : ℕ}
  {g : E n → ℂ} :
-- imply
  Function.HasTemperateGrowth g ↔ Function.HasTemperateGrowth (g ∘ Neg.neg) :=
-- proof
  ⟨hasTemperateGrowth_comp_neg,
    fun h => by rw [show g = (g ∘ Neg.neg) ∘ Neg.neg from by ext; simp]
      exact hasTemperateGrowth_comp_neg h⟩

end ConeSupport

namespace ConeSupport

/--
[smulLeft_reflection_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma smulLeft_reflection_eq
  {n : ℕ}
  {g : E n → ℂ}
  {v : TemperedDistribution (E n) ℂ} :
-- imply
  TemperedDistribution.smulLeftCLM ℂ g (reflection v) = (TemperedDistribution.smulLeftCLM ℂ (g ∘ Neg.neg) v).comp schwartzReflectionCLM := by
-- proof
  ext φ
  show v (schwartzReflectionCLM ((SchwartzMap.smulLeftCLM ℂ g) φ)) =
    v ((SchwartzMap.smulLeftCLM ℂ (g ∘ Neg.neg)) (schwartzReflectionCLM φ))
  congr 1
  ext x
  simp only [schwartzReflectionCLM, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp, ContinuousLinearEquiv.coe_neg, SchwartzMap.smulLeftCLM]
  split_ifs with h1 h2 h2
  · simp only [SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp, ContinuousLinearEquiv.coe_neg]
    simp [Pi.neg_apply, id]
  · exact absurd (hasTemperateGrowth_comp_neg h1) h2
  · exact absurd (hasTemperateGrowth_neg_iff.mpr h2) h1
  · simp

end ConeSupport

namespace ConeSupport

/--
[reflection_schwartz_coercion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma reflection_schwartz_coercion
  {n : ℕ}
  {f : SchwartzMap (E n) ℂ} :
-- imply
  (↑f : 𝓢'(E n, ℂ)).comp schwartzReflectionCLM = (↑(schwartzReflectionCLM f) : 𝓢'(E n, ℂ)) := by
-- proof
  ext φ
  simp only [ContinuousLinearMap.comp_apply]
  change (SchwartzMap.toTemperedDistributionCLM (E n) ℂ volume f) (schwartzReflectionCLM φ) =
    (SchwartzMap.toTemperedDistributionCLM (E n) ℂ volume (schwartzReflectionCLM f)) φ
  rw [SchwartzMap.toTemperedDistributionCLM_apply_apply (μ := volume),
    SchwartzMap.toTemperedDistributionCLM_apply_apply (μ := volume)]
  simp_rw [schwartzReflectionCLM, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp, ContinuousLinearEquiv.coe_neg]
  simp only [Pi.neg_apply, id]
  conv_lhs => rw [← Measure.map_neg_eq_self (μ := (volume : Measure (E n)))]
  rw [integral_map (Measurable.aemeasurable measurable_neg)]
  · simp [neg_neg]
  · rw [Measure.map_neg_eq_self]
    exact ((SchwartzMap.continuous φ).comp continuous_neg).aestronglyMeasurable.smul
      (SchwartzMap.continuous f).aestronglyMeasurable

end ConeSupport

namespace ConeSupport

/--
[schwartzReflectionCLM_comp_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma schwartzReflectionCLM_comp_self
  {n : ℕ} :
-- imply
  schwartzReflectionCLM.comp (schwartzReflectionCLM (n := n)) = ContinuousLinearMap.id ℂ _ := by
-- proof
  ext φ x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    schwartzReflectionCLM, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp, ContinuousLinearEquiv.coe_neg, Pi.neg_apply, id, neg_neg]

end ConeSupport

namespace ConeSupport

/--
[reflection_reflection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma reflection_reflection
  {n : ℕ}
  {u : TemperedDistribution (E n) ℂ} :
-- imply
  reflection (reflection u) = u := by
-- proof
  simp only [reflection]
  rw [ContinuousLinearMap.comp_assoc, schwartzReflectionCLM_comp_self,
    ContinuousLinearMap.comp_id]

end ConeSupport

namespace ConeSupport

/--
[isConicCutoffNear_comp_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma isConicCutoffNear_comp_neg
  {n : ℕ}
  {g : E n → ℂ}
  {ω : Sphere n}
-- given
  (hg : IsConicCutoffNear g ω) :
-- imply
  IsConicCutoffNear (g ∘ Neg.neg) (sphereNeg ω) := by
-- proof
  obtain ⟨hsmooth, R, hR, _, R₀, hR₀, hsupp, ψ, hhom, hψω, hagree⟩ := hg
  refine ⟨hsmooth.comp (ContinuousLinearEquiv.neg ℝ).contDiff,
    R, hR, ‹_›, R₀, hR₀, ?_, ψ ∘ Neg.neg, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Function.mem_support, Function.comp_apply] at hx
    have := hsupp (show -x ∈ Function.support g from by simp [Function.mem_support, hx])
    simp only [mem_setOf_eq] at this ⊢
    rwa [norm_neg] at this
  · intro a ha x hx
    simp only [Function.comp_apply]
    rw [← smul_neg]
    exact hhom a ha (-x) (neg_ne_zero.mpr hx)
  · simp only [Function.comp_apply, sphereNeg_val, neg_neg]
    exact hψω
  · intro x hx
    simp only [Function.comp_apply]
    exact hagree (-x) (by rwa [norm_neg])

end ConeSupport

namespace ConeSupport

/--
[css_reflection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma css_reflection
  {n : ℕ}
  {v : TemperedDistribution (E n) ℂ} :
-- imply
  ConicSingularSupportSphere (reflection v) = negSet (ConicSingularSupportSphere v) := by
-- proof
  ext ω
  rw [mem_negSet_iff]
  simp only [ConicSingularSupportSphere, mem_setOf_eq]
  constructor
  ·
    intro hω hcontra
    apply hω
    obtain ⟨g, hg_conic, f, hf⟩ := hcontra
    refine ⟨g ∘ Neg.neg, ?_, ?_⟩
    · have := isConicCutoffNear_comp_neg hg_conic
      rwa [sphereNeg_sphereNeg] at this
    · rw [smulLeft_reflection_eq]
      have hgg : (g ∘ Neg.neg) ∘ Neg.neg = g := by ext; simp
      rw [hgg, hf]
      exact ⟨schwartzReflectionCLM f, reflection_schwartz_coercion f⟩
  ·
    intro hω hcontra
    apply hω
    obtain ⟨g, hg_conic, f, hf⟩ := hcontra
    refine ⟨g ∘ Neg.neg, isConicCutoffNear_comp_neg hg_conic, ?_⟩
    have h1 : reflection (TemperedDistribution.smulLeftCLM ℂ (g ∘ Neg.neg) v) = ↑f := by
      show (TemperedDistribution.smulLeftCLM ℂ (g ∘ Neg.neg) v).comp schwartzReflectionCLM =
        (f : 𝓢'(E n, ℂ))
      rwa [← smulLeft_reflection_eq]
    have h2 : TemperedDistribution.smulLeftCLM ℂ (g ∘ Neg.neg) v = reflection (↑f) := by
      have h3 := congr_arg reflection h1
      rwa [reflection_reflection] at h3
    rw [h2]
    exact ⟨schwartzReflectionCLM f, reflection_schwartz_coercion f⟩

end ConeSupport

namespace ConeSupport

/--
[norm_smul_sub_smul_lower_bound'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma norm_smul_sub_smul_lower_bound'
  {n : ℕ}
  {X Y : E n}
  {r s : ℝ}
-- given
  (hX : ‖X‖ = 1)
  (hY : ‖Y‖ = 1)
  (hr : 0 ≤ r)
  (hs : 0 ≤ s) :
-- imply
  ‖X - Y‖ / 2 * (r + s) ≤ ‖r • X - s • Y‖ := by
-- proof
  suffices h : (‖X - Y‖ / 2 * (r + s)) ^ 2 ≤ ‖r • X - s • Y‖ ^ 2 from
    le_of_sq_le_sq h (norm_nonneg _)
  have hRHS : ‖r • X - s • Y‖ ^ 2 = r ^ 2 + s ^ 2 - 2 * (r * s * (inner (𝕜 := ℝ) X Y)) := by
    rw [norm_sub_sq_real, norm_smul, norm_smul,
      Real.norm_of_nonneg hr, Real.norm_of_nonneg hs, hX, hY, mul_one, mul_one,
      real_inner_smul_left, inner_smul_right]; ring
  have hnorm_sq : ‖X - Y‖ ^ 2 = 2 - 2 * (inner (𝕜 := ℝ) X Y) := by
    rw [norm_sub_sq_real, hX, hY]; ring
  rw [show (‖X - Y‖ / 2 * (r + s)) ^ 2 = ‖X - Y‖ ^ 2 / 4 * (r + s) ^ 2 from by ring,
    hnorm_sq, hRHS]
  have ht_bound : (-1 : ℝ) ≤ inner (𝕜 := ℝ) X Y := by
    have := abs_real_inner_le_norm X Y
    rw [hX, hY, mul_one] at this
    linarith [neg_abs_le (inner (𝕜 := ℝ) X Y)]
  nlinarith [sq_nonneg (r - s)]

end ConeSupport

namespace ConeSupport

/--
[conicCutoff_direction_separation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma conicCutoff_direction_separation
  {n : ℕ}
  {g : E n → ℂ}
  {ω : Sphere n}
  {Γ : Set (Sphere n)}
-- given
  (_hg : IsConicCutoffNear g ω)
  (_hωΓ : ω ∈ Γ)
  (hΓ_open : IsOpen Γ)
  (hdir_in : closure {σ : Sphere n | ∃ (x : E n) (hx : x ≠ 0), g x ≠ 0 ∧ directionOf x hx = σ} ⊆ Γ) :
-- imply
  ∃ (δ : ℝ), 0 < δ ∧ ∀ (x : E n), g x ≠ 0 → (hx : x ≠ 0) → ∀ (y : E n) (hy : y ≠ 0), directionOf y hy ∉ Γ → δ ≤ ‖(directionOf x hx : E n) - (directionOf y hy : E n)‖ := by
-- proof
  set D := {σ : Sphere n | ∃ (x : E n) (hx : x ≠ 0), g x ≠ 0 ∧ directionOf x hx = σ}
  have hcl_compact : IsCompact (closure D) := isClosed_closure.isCompact
  obtain ⟨δ, hδ, hthick⟩ := hcl_compact.exists_thickening_subset_open hΓ_open hdir_in
  refine ⟨δ, hδ, fun x hgx hx y hy hy_dir => ?_⟩
  have hx_in_cl : directionOf x hx ∈ closure D :=
    subset_closure ⟨x, hx, hgx, rfl⟩
  by_contra h_lt
  push Not at h_lt
  have hy_in_thick : directionOf y hy ∈ Metric.thickening δ (closure D) := by
    rw [Metric.mem_thickening_iff]
    refine ⟨directionOf x hx, hx_in_cl, ?_⟩
    simp only [Subtype.dist_eq, dist_eq_norm]
    linarith [norm_sub_rev (↑(directionOf x hx) : E n) (↑(directionOf y hy) : E n)]
  exact hy_dir (hthick hy_in_thick)

end ConeSupport

namespace ConeSupport

/--
[coneSeparation_estimate_conic_cutoff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma coneSeparation_estimate_conic_cutoff
  {n : ℕ}
  {g : E n → ℂ}
  {ω : Sphere n}
  {Γ : Set (Sphere n)}
  {ε : ℝ}
-- given
  (hg : IsConicCutoffNear g ω)
  (hωΓ : ω ∈ Γ)
  (hΓ_open : IsOpen Γ)
  (hdir_in : closure {σ : Sphere n | ∃ (x : E n) (hx : x ≠ 0), g x ≠ 0 ∧ directionOf x hx = σ} ⊆ Γ)
  (hε : 0 < ε) :
-- imply
  ∃ (c : ℝ), 0 < c ∧ ∀ (x y : E n), g x ≠ 0 → (hy : y ≠ 0) → directionOf y hy ∉ Γ → ε ≤ ‖y‖ → c * (‖x‖ + ‖y‖) ≤ ‖x - y‖ := by
-- proof
  obtain ⟨_, _, _, R₀, hR₀, hsupp, _⟩ := hg.2
  obtain ⟨δ, hδ, hsep⟩ := conicCutoff_direction_separation g ω hg Γ hωΓ hΓ_open hdir_in
  refine ⟨δ / 2, by positivity, fun x y hgx hy hdir hεy => ?_⟩
  have hx_ne : x ≠ 0 := by
    intro h; subst h
    exact absurd (hsupp (Function.mem_support.mpr hgx)) (by simp; linarith)
  have hx_pos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx_ne
  have hy_pos : (0 : ℝ) < ‖y‖ := lt_of_lt_of_le hε hεy
  have hdir_x : ‖(directionOf x hx_ne : E n)‖ = 1 := by
    have := (directionOf x hx_ne).2
    rwa [Metric.mem_sphere, dist_zero_right] at this
  have hdir_y : ‖(directionOf y hy : E n)‖ = 1 := by
    have := (directionOf y hy).2
    rwa [Metric.mem_sphere, dist_zero_right] at this
  have hx_eq : x = ‖x‖ • (directionOf x hx_ne : E n) := by
    simp [directionOf, smul_smul, mul_inv_cancel₀ (ne_of_gt hx_pos)]
  have hy_eq : y = ‖y‖ • (directionOf y hy : E n) := by
    simp [directionOf, smul_smul, mul_inv_cancel₀ (ne_of_gt hy_pos)]
  calc δ / 2 * (‖x‖ + ‖y‖)
    ≤ ‖(directionOf x hx_ne : E n) - (directionOf y hy : E n)‖ / 2 * (‖x‖ + ‖y‖) := by
      gcongr
      exact hsep x hgx hx_ne y hy hdir
    _ ≤ ‖‖x‖ • (directionOf x hx_ne : E n) - ‖y‖ • (directionOf y hy : E n)‖ :=
      norm_smul_sub_smul_lower_bound' _ _ hdir_x hdir_y _ _ (le_of_lt hx_pos) (le_of_lt hy_pos)
    _ = ‖x - y‖ := by rw [← hx_eq, ← hy_eq]

end ConeSupport

namespace ConeSupport

/--
[isConicCutoffNear_hasTemperateGrowth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma isConicCutoffNear_hasTemperateGrowth
  {n : ℕ}
  {g : E n → ℂ}
  {ω : Sphere n}
-- given
  (hg : IsConicCutoffNear g ω) :
-- imply
  Function.HasTemperateGrowth g := by
-- proof
  obtain ⟨hg_smooth, R, hR, _, R₀, hR₀, hsupp, ψ, hψ_hom, _, hψ_eq⟩ := hg
  refine ⟨hg_smooth, fun m => ?_⟩
  have h_cont_m : Continuous (iteratedFDeriv ℝ m g) :=
    hg_smooth.continuous_iteratedFDeriv (mod_cast le_top)
  obtain ⟨C_ball, hC_ball⟩ := (isCompact_closedBall (0 : E n) (R + 1)).exists_bound_of_continuousOn
    h_cont_m.norm.continuousOn
  refine ⟨0, C_ball, fun x => ?_⟩
  simp only [pow_zero, mul_one]
  by_cases hx : ‖x‖ ≤ R + 1
  · have hx_ball : x ∈ Metric.closedBall (0 : E n) (R + 1) := by
    simp [Metric.mem_closedBall, dist_zero_right]; exact hx
    have := hC_ball x hx_ball
    rwa [Real.norm_of_nonneg (norm_nonneg _)] at this
  · simp only [not_le] at hx
    have hx_gt_R : R < ‖x‖ := by linarith
    have hx_pos : (0 : ℝ) < ‖x‖ := by linarith
    have hx_ne : x ≠ 0 := by intro h; rw [h, norm_zero] at hx_pos; linarith
    set a := (R + 1) / ‖x‖ with ha_def
    have ha_pos : 0 < a := div_pos (by linarith) hx_pos
    have ha_le_one : a ≤ 1 := by rw [ha_def, div_le_one hx_pos]; linarith
    have ha_x_norm : ‖a • x‖ = R + 1 := by
      rw [norm_smul, Real.norm_of_nonneg ha_pos.le, ha_def]; field_simp
    have ha_x_ball : a • x ∈ Metric.closedBall (0 : E n) (R + 1) := by
      simp [Metric.mem_closedBall, dist_zero_right, ha_x_norm]
    have hg_comp_eq : (fun y => g (a • y)) =ᶠ[nhds x] g := by
      have hopen : IsOpen {y : E n | R < ‖y‖ ∧ R < ‖a • y‖} := by
        apply IsOpen.inter (isOpen_lt continuous_const continuous_norm)
        exact isOpen_lt continuous_const (continuous_norm.comp (continuous_const.smul continuous_id))
      have hx_mem : x ∈ {y : E n | R < ‖y‖ ∧ R < ‖a • y‖} := by
        refine ⟨hx_gt_R, ?_⟩; rw [ha_x_norm]; linarith
      exact Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨{y | R < ‖y‖ ∧ R < ‖a • y‖}, hopen.mem_nhds hx_mem, fun y ⟨hy1, hy2⟩ => by
          have hyne : y ≠ 0 := by intro h; rw [h, norm_zero] at hy1; linarith
          simp only
          rw [hψ_eq (a • y) hy2, hψ_hom a ha_pos y hyne, ← hψ_eq y hy1]⟩
    have hderiv_eq : iteratedFDeriv ℝ m g x = iteratedFDeriv ℝ m (fun y => g (a • y)) x :=
      ((hg_comp_eq.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds).symm
    have hfunc_eq : (fun y => g (a • y)) = g ∘ (a • ContinuousLinearMap.id ℝ (E n)) := by
      ext y; simp
    have hcomp_formula : iteratedFDeriv ℝ m (g ∘ (a • ContinuousLinearMap.id ℝ (E n))) x =
      (iteratedFDeriv ℝ m g (a • x)).compContinuousLinearMap
        (fun _ => a • ContinuousLinearMap.id ℝ (E n)) :=
      ContinuousLinearMap.iteratedFDeriv_comp_right
        (a • ContinuousLinearMap.id ℝ (E n)) hg_smooth x (mod_cast le_top)
    rw [hderiv_eq, hfunc_eq, hcomp_formula]
    have hball_bound : ‖iteratedFDeriv ℝ m g (a • x)‖ ≤ C_ball := by
      have := hC_ball (a • x) ha_x_ball
      rwa [Real.norm_of_nonneg (norm_nonneg _)] at this
    have hprod_le_one : ∏ _ : Fin m, ‖a • ContinuousLinearMap.id ℝ (E n)‖ ≤ 1 := by
      apply Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => ?_)
      calc ‖a • ContinuousLinearMap.id ℝ (E n)‖
        ≤ ‖a‖ * ‖ContinuousLinearMap.id ℝ (E n)‖ := ContinuousLinearMap.opNorm_smul_le a _
        _ ≤ ‖a‖ * 1 := by gcongr; exact ContinuousLinearMap.norm_id_le
        _ = a := by rw [mul_one, Real.norm_of_nonneg ha_pos.le]
        _ ≤ 1 := ha_le_one
    calc ‖(iteratedFDeriv ℝ m g (a • x)).compContinuousLinearMap
      (fun _ => a • ContinuousLinearMap.id ℝ (E n))‖
      ≤ ‖iteratedFDeriv ℝ m g (a • x)‖ * ∏ _ : Fin m,
        ‖a • ContinuousLinearMap.id ℝ (E n)‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ C_ball * 1 := by
        apply mul_le_mul hball_bound hprod_le_one (Finset.prod_nonneg (fun i _ => norm_nonneg _))
          (le_trans (norm_nonneg _) hball_bound)
      _ = C_ball := mul_one _

end ConeSupport

namespace ConeSupport

/--
[isCompactlySupportedDistribution_hasCompactDsupport](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma isCompactlySupportedDistribution_hasCompactDsupport
  {n : ℕ}
  {u : 𝓢'(E n, ℂ)}
-- given
  (hu : IsCompactlySupportedDistribution u) :
-- imply
  DifferentialOperators.HasCompactDsupport u := by
-- proof
  obtain ⟨K, hK_compact, hK_vanish⟩ := hu
  unfold DifferentialOperators.HasCompactDsupport
  have hK_closed : IsClosed K := hK_compact.isClosed
  have hsub : Distribution.dsupport u ⊆ K := by
    intro x hx
    rw [Distribution.mem_dsupport_iff] at hx
    apply hx K
    · intro ψ hψ
      apply hK_vanish
      ext z
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hz_supp hz_K
      exact (hψ (subset_tsupport _ hz_supp)) hz_K
    · exact hK_closed
  exact hK_compact.of_isClosed_subset Distribution.isClosed_dsupport hsub

end ConeSupport

namespace ConeSupport

/--
[smulLeftCLM_schwEmbed_eq_local](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma smulLeftCLM_schwEmbed_eq_local
  {n : ℕ}
  {g : E n → ℂ}
  {f : 𝓢(E n, ℂ)} :
-- imply
  TemperedDistribution.smulLeftCLM ℂ g (schwEmbed f) = schwEmbed (SchwartzMap.smulLeftCLM ℂ g f) := by
-- proof
  ext ψ
  simp only [TemperedDistribution.smulLeftCLM_apply_apply]
  simp only [schwEmbed, SchwartzMap.toTemperedDistributionCLM_apply_apply]
  congr 1
  ext x
  by_cases hg : Function.HasTemperateGrowth g
  · simp only [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]
    ring
  · have : SchwartzMap.smulLeftCLM ℂ g = (0 : 𝓢(E n, ℂ) →L[ℂ] 𝓢(E n, ℂ)) := by
    unfold SchwartzMap.smulLeftCLM
    exact dif_neg hg
    simp [this]

end ConeSupport

namespace ConeSupport

/--
[schwartzConvolution_schwEmbed_eq_schwEmbed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma schwartzConvolution_schwEmbed_eq_schwEmbed
  {n : ℕ}
  {u₂ : 𝓢(E n, ℂ)}
  {φ : 𝓢(E n, ℂ)} :
-- imply
  schwartzConvolution (schwEmbed u₂) φ = schwEmbed (((SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)) φ) u₂) := by
-- proof
  ext ψ
  change (schwEmbed u₂)
    (((SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)) (schwartzReflectionCLM φ)) ψ) = _
  simp only [SchwartzMap.toTemperedDistributionCLM_apply_apply]
  simp_rw [SchwartzMap.convolution_apply, convolution_mul_swap]
  have hrefl : ∀ (a b : E n), (schwartzReflectionCLM φ) (a - b) = φ (b - a) := by
    intro a b
    simp [schwartzReflectionCLM, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Function.comp, neg_sub]
  simp_rw [hrefl, smul_eq_mul]
  conv_lhs =>
    arg 2; ext x
    rw [show (∫ t, φ (t - x) * ψ t) * u₂ x =
      ∫ t, φ (t - x) * ψ t * u₂ x from (integral_mul_const (u₂ x) _).symm]
  conv_rhs =>
    arg 2; ext x
    rw [show ψ x * ∫ t, φ (x - t) * u₂ t =
      ∫ t, ψ x * (φ (x - t) * u₂ t) from (integral_const_mul (ψ x) _).symm]
  rw [integral_integral_swap]
  congr 1; ext a; congr 1; ext b; ring
  ·
    set C := ‖φ.toBoundedContinuousFunction‖
    have hC : ∀ y : E n, ‖φ y‖ ≤ C :=
      fun y => φ.toBoundedContinuousFunction.norm_coe_le_norm y
    have hprod := (u₂.integrable (μ := volume)).mul_prod (ψ.integrable (μ := volume))
    refine (hprod.norm.const_mul C).mono' ?_ ?_
    · apply AEStronglyMeasurable.mul
      · exact ((φ.continuous.comp (continuous_snd.sub continuous_fst)).aestronglyMeasurable).mul
        (ψ.continuous.comp continuous_snd).aestronglyMeasurable
      · exact (u₂.continuous.comp continuous_fst).aestronglyMeasurable
    · filter_upwards with ⟨x, t⟩
      simp only [Function.uncurry_apply_pair, norm_mul]
      have h1 := hC (t - x)
      have h2 := norm_nonneg (ψ t)
      have h3 := norm_nonneg (u₂ x)
      rw [show ‖φ (t - x)‖ * ‖ψ t‖ * ‖u₂ x‖ = ‖φ (t - x)‖ * (‖ψ t‖ * ‖u₂ x‖) from
        mul_assoc _ _ _]
      rw [show C * (‖u₂ x‖ * ‖ψ t‖) = C * (‖ψ t‖ * ‖u₂ x‖) from by ring]
      exact mul_le_mul_of_nonneg_right h1 (mul_nonneg h2 h3)

end ConeSupport

namespace ConeSupport

/--
[conicCutoff_smul_schwartzConvolution_schwartz_schwartz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma conicCutoff_smul_schwartzConvolution_schwartz_schwartz
  {n : ℕ}
  {u₂ : 𝓢(E n, ℂ)}
  {φ : 𝓢(E n, ℂ)}
  {g₀ : E n → ℂ}
  {ω : Sphere n}
-- given
  (_hg₀ : IsConicCutoffNear g₀ ω) :
-- imply
  ∃ (f : SchwartzMap (E n) ℂ), TemperedDistribution.smulLeftCLM ℂ g₀ (schwartzConvolution (schwEmbed u₂) φ) = (f : 𝓢'(E n, ℂ)) := by
-- proof
  rw [schwartzConvolution_schwEmbed_eq_schwEmbed]
  rw [smulLeftCLM_schwEmbed_eq_local]
  exact ⟨_, rfl⟩

end ConeSupport

namespace ConeSupport

/--
[schwartzConvolution_add_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma schwartzConvolution_add_left
  {n : ℕ}
  {u₁ u₂ : TemperedDistribution (E n) ℂ}
  {φ : 𝓢(E n, ℂ)} :
-- imply
  schwartzConvolution (u₁ + u₂) φ = schwartzConvolution u₁ φ + schwartzConvolution u₂ φ := by
-- proof
  simp only [schwartzConvolution]
  exact ContinuousLinearMap.add_comp u₁ u₂ _

end ConeSupport

namespace ConeSupport

/--
[smulLeftCLM_add_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma smulLeftCLM_add_right
  {n : ℕ}
  {g : E n → ℂ}
  {u₁ u₂ : TemperedDistribution (E n) ℂ} :
-- imply
  TemperedDistribution.smulLeftCLM ℂ g (u₁ + u₂) = TemperedDistribution.smulLeftCLM ℂ g u₁ + TemperedDistribution.smulLeftCLM ℂ g u₂ :=
-- proof
  map_add (TemperedDistribution.smulLeftCLM ℂ g) u₁ u₂

end ConeSupport

namespace ConeSupport

/--
[disjointCssCondition_iff_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma disjointCssCondition_iff_disjoint
  {n : ℕ}
  {u v : TemperedDistribution (E n) ℂ} :
-- imply
  DisjointCssCondition u v ↔ Disjoint (ConicSingularSupportSphere u) (negSet (ConicSingularSupportSphere v)) := by
-- proof
  constructor
  · intro h
    rw [Set.disjoint_left]
    intro ω hωu hωneg
    exact h ω hωu (mem_negSet_iff.mp hωneg)
  · intro h ω hωu hωv
    exact Set.disjoint_left.mp h hωu (mem_negSet_iff.mpr hωv)

end ConeSupport

namespace ConeSupport

/--
[exists_conic_cutoff_from_homogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma exists_conic_cutoff_from_homogeneous
  {n : ℕ}
  {ψ : E n → ℂ}
-- given
  (hψ_hom : ∀ (a : ℝ), 0 < a → ∀ (x : E n), x ≠ 0 → ψ (a • x) = ψ x)
  (hψ_smooth : ContDiffOn ℝ ⊤ ψ {x : E n | x ≠ 0}) :
-- imply
  ∃ (g : E n → ℂ) (hg_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (R₁ R₂ : ℝ) (hR₁ : 0 < R₁) (hR₂ : R₁ < R₂), Function.support g ⊆ {x : E n | R₁ ≤ ‖x‖} ∧ (∀ x : E n, R₂ < ‖x‖ → g x = ψ x) := by
-- proof
  have hlt : (1 : ℝ) < 2 := by norm_num
  let χ : ContDiffBump (0 : E n) := ⟨1, 2, one_pos, hlt⟩
  refine ⟨fun x => ψ x * (1 - (χ x : ℂ)), ?_, 1, 2, one_pos, hlt, ?_, ?_⟩
  ·
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Metric.ball (0 : E n) 1
    ·
      have h1 := χ.eventuallyEq_one_of_mem_ball hx
      have hev : (fun y => ψ y * (1 - (χ y : ℂ))) =ᶠ[nhds x] (fun _ => (0 : ℂ)) := by
        filter_upwards [h1] with y hy
        simp [show (χ : E n → ℝ) y = 1 from hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    ·
      have hxne : x ≠ 0 := by
        intro h; apply hx; rw [h]; exact Metric.mem_ball_self one_pos
      have hψ_at : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ x :=
        ((hψ_smooth x (Set.mem_setOf.mpr hxne)).contDiffAt
          (IsOpen.mem_nhds isOpen_ne hxne)).of_le le_top
      have hχ_at : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (1 : ℂ) - (χ y : ℂ)) x :=
        ContDiffAt.sub contDiffAt_const
          ((Complex.ofRealCLM.contDiff.comp χ.contDiff).contDiffAt)
      exact hψ_at.mul hχ_at
  ·
    intro x hx
    simp only [Function.mem_support] at hx
    simp only [Set.mem_setOf_eq]
    by_contra h
    push_neg at h
    have hxball : x ∈ Metric.closedBall (0 : E n) 1 := by
      simp only [Metric.mem_closedBall, dist_zero_right]; linarith
    have hchi : (χ : E n → ℝ) x = 1 := χ.one_of_mem_closedBall hxball
    simp [hchi] at hx
  ·
    intro x hx
    have hxball : x ∉ Metric.ball (0 : E n) 2 := by
      simp only [Metric.mem_ball, dist_zero_right, not_lt]; linarith
    have hsupp : x ∉ Function.support (χ : E n → ℝ) := by
      rw [χ.support_eq]; exact hxball
    have hchi : (χ : E n → ℝ) x = 0 := Function.notMem_support.mp hsupp
    simp [hchi]

end ConeSupport

namespace ConeSupport

/--
[smooth_homogeneous_support_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma smooth_homogeneous_support_contradiction
  {n : ℕ}
  {g : E n → ℂ}
  {R : ℝ}
  {ψ : E n → ℂ}
-- given
  (hg_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
  (hR : 0 < R)
  (hg_supp : Function.support g ⊆ {x : E n | R ≤ ‖x‖})
  (hψ_hom : ∀ (a : ℝ), 0 < a → ∀ (x : E n), x ≠ 0 → ψ (a • x) = ψ x)
  (hg_eq : ∀ x : E n, R < ‖x‖ → g x = ψ x)
  (hψ_nonzero : ¬∀ ω : Sphere n, ψ (↑ω) = 0) :
-- imply
  False := by
-- proof
  rw [not_forall] at hψ_nonzero
  obtain ⟨ω₀, hω₀_ne⟩ := hψ_nonzero
  change ψ (↑ω₀) ≠ 0 at hω₀_ne
  have hω₀_norm : ‖(↑ω₀ : E n)‖ = 1 := by
    have := ω₀.2; rw [Metric.mem_sphere, dist_zero_right] at this; exact this
  have hω₀_ne_zero : (↑ω₀ : E n) ≠ 0 := by intro h; simp [h] at hω₀_norm
  set f := fun t : ℝ => g (t • (↑ω₀ : E n))
  have hf_cont : Continuous f :=
    hg_smooth.continuous.comp (continuous_id.smul continuous_const)
  have hf_zero : ∀ t ∈ Set.Ioo (0 : ℝ) R, f t = 0 := by
    intro t ⟨ht_pos, ht_lt⟩
    have h_not_supp : t • (↑ω₀ : E n) ∉ Function.support g := by
      intro hmem
      have h := hg_supp hmem
      simp only [Set.mem_setOf_eq] at h
      rw [norm_smul, hω₀_norm, mul_one, Real.norm_of_nonneg ht_pos.le] at h
      linarith
    simp [Function.support] at h_not_supp
    exact h_not_supp
  have hf_psi : ∀ t ∈ Set.Ioi R, f t = ψ (↑ω₀) := by
    intro t ht
    have ht_pos : 0 < t := lt_trans hR ht
    have ht_norm : R < ‖t • (↑ω₀ : E n)‖ := by
      rw [norm_smul, hω₀_norm, mul_one, Real.norm_of_nonneg ht_pos.le]; exact ht
    show g (t • (↑ω₀ : E n)) = ψ (↑ω₀)
    rw [hg_eq _ ht_norm, hψ_hom t ht_pos (↑ω₀) hω₀_ne_zero]
  have hfR_zero : f R = 0 := by
    have h_closed : IsClosed (f ⁻¹' {0}) := isClosed_singleton.preimage hf_cont
    have h_sub : Set.Ioo 0 R ⊆ f ⁻¹' {0} := fun t ht => by simp [hf_zero t ht]
    have h_R_mem : R ∈ closure (Set.Ioo (0 : ℝ) R) := by
      rw [closure_Ioo (ne_of_lt hR)]; exact ⟨hR.le, le_refl R⟩
    exact Set.mem_singleton_iff.mp (h_closed.closure_subset_iff.mpr h_sub h_R_mem)
  have hfR_psi : f R = ψ (↑ω₀) := by
    have h_closed : IsClosed (f ⁻¹' {ψ (↑ω₀)}) := isClosed_singleton.preimage hf_cont
    have h_sub : Set.Ioi R ⊆ f ⁻¹' {ψ (↑ω₀)} := fun t ht => by simp [hf_psi t ht]
    have h_R_mem : R ∈ closure (Set.Ioi R) := closure_Ioi R ▸ Set.self_mem_Ici
    exact Set.mem_singleton_iff.mp (h_closed.closure_subset_iff.mpr h_sub h_R_mem)
  exact hω₀_ne (hfR_psi.symm.trans hfR_zero)
set_option linter.unusedVariables false in

end ConeSupport

namespace ConeSupport

/--
[partition_of_unity_schwartz_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma partition_of_unity_schwartz_factorization
  {n : ℕ}
  {u : 𝓢'(E n, ℂ)}
  {g : E n → ℂ}
  {R : ℝ}
  {ψ : E n → ℂ}
-- given
  (hg_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
  (hR : 0 < R)
  (hg_supp : Function.support g ⊆ {x : E n | R ≤ ‖x‖})
  (hψ_hom : ∀ (a : ℝ), 0 < a → ∀ (x : E n), x ≠ 0 → ψ (a • x) = ψ x)
  (hg_eq : ∀ x : E n, R < ‖x‖ → g x = ψ x)
  (_hwitness : ∀ ω : Sphere n, ψ (↑ω) ≠ 0 → ∃ (g_ω : E n → ℂ), IsConicCutoffNear g_ω ω ∧ ∃ (f_ω : SchwartzMap (E n) ℂ), TemperedDistribution.smulLeftCLM ℂ g_ω u = (f_ω : 𝓢'(E n, ℂ)))
  (hψ_nonzero : ¬∀ ω : Sphere n, ψ (↑ω) = 0) :
-- imply
  ∃ (μ : E n → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ ∧ Function.HasTemperateGrowth μ ∧ (∃ (f_μ : SchwartzMap (E n) ℂ), TemperedDistribution.smulLeftCLM ℂ μ u = (f_μ : 𝓢'(E n, ℂ))) ∧ HasCompactSupport (fun x => g x * (μ x)⁻¹) ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => g x * (μ x)⁻¹) ∧ (∀ x, μ x ≠ 0 → g x * (μ x)⁻¹ * μ x = g x) ∧ (∀ x, μ x = 0 → g x = 0) :=
-- proof
  (smooth_homogeneous_support_contradiction g hg_smooth R hR hg_supp ψ
    hψ_hom hg_eq hψ_nonzero).elim
set_option maxHeartbeats 400000 in

end ConeSupport

namespace ConeSupport

/--
[contDiff_div_of_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma contDiff_div_of_support_subset
  {n : ℕ}
  [NormedAddCommGroup V]
  [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
  {φ φ' : V → ℂ}
-- given
  (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
  (hφ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ')
  (hsup : tsupport φ' ⊆ Function.support φ) :
-- imply
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => φ' x * (φ x)⁻¹) := by
-- proof
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : φ x ≠ 0
  ·
    exact hφ'.contDiffAt.mul (hφ.contDiffAt.inv hx)
  ·
    push Not at hx
    have hx_not_supp : x ∉ tsupport φ' := fun hmem =>
      absurd (hsup hmem) (Function.notMem_support.mpr hx)
    have hφ'_eq : φ' =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx_not_supp
    have hμ_eq : (fun y => φ' y * (φ y)⁻¹) =ᶠ[nhds x] (fun _ => (0 : ℂ)) := by
      filter_upwards [hφ'_eq] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq hμ_eq

end ConeSupport

namespace ConeSupport

/--
[smooth_factorization_smulLeftCLM](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma smooth_factorization_smulLeftCLM
  {n : ℕ}
  {u : 𝓢'(E n, ℂ)}
  {φ φ' : E n → ℂ}
-- given
  (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
  (hφc : HasCompactSupport φ)
  (hφ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ')
  (hφ'c : HasCompactSupport φ')
  (hsup : tsupport φ' ⊆ Function.support φ) :
-- imply
  ∃ (μ : E n → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ ∧ HasCompactSupport μ ∧ TemperedDistribution.smulLeftCLM ℂ φ' u = TemperedDistribution.smulLeftCLM ℂ μ (TemperedDistribution.smulLeftCLM ℂ φ u) := by
-- proof
  have hsup' : Function.support φ' ⊆ Function.support φ :=
    (subset_tsupport φ').trans hsup
  set μ := fun x => φ' x * (φ x)⁻¹ with hμ_def
  have hμ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ :=
    contDiff_div_of_support_subset hφ hφ' hsup
  have hμ_compact : HasCompactSupport μ :=
    hφ'c.mono (fun x hx => by
      simp only [hμ_def, Function.mem_support] at hx ⊢; exact left_ne_zero_of_mul hx)
  refine ⟨μ, hμ_smooth, hμ_compact, ?_⟩
  have hφ_temp : Function.HasTemperateGrowth φ := hφc.hasTemperateGrowth hφ
  have hμ_temp : Function.HasTemperateGrowth μ := hμ_compact.hasTemperateGrowth hμ_smooth
  have heq : φ * μ = φ' := by
    ext x; simp only [Pi.mul_apply, hμ_def]
    by_cases hφx : φ x = 0
    · have : φ' x = 0 := by
      by_contra h
      exact absurd (Function.mem_support.mp (hsup' (Function.mem_support.mpr h)))
        (not_not.mpr hφx)
      simp [hφx, this]
    · field_simp
  rw [show TemperedDistribution.smulLeftCLM ℂ μ (TemperedDistribution.smulLeftCLM ℂ φ u)
    = TemperedDistribution.smulLeftCLM ℂ (φ * μ) u from
    (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hφ_temp hμ_temp u)]
  rw [heq]

end ConeSupport

namespace ConeSupport

/--
[fourier_schwartzReflection_fourier](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma fourier_schwartzReflection_fourier
  {n : ℕ}
  {g : 𝓢(E n, ℂ)} :
-- imply
  𝓕 (schwartzReflectionCLM (𝓕 g)) = g := by
-- proof
  have h1 : 𝓕⁻ g = schwartzReflectionCLM (𝓕 g) := by
    simp only [FourierTransformInv.fourierInv, schwartzReflectionCLM]
    simp only [ContinuousLinearMap.comp_apply, SchwartzMap.fourierTransformCLM_apply]
    rfl
  rw [← h1]
  exact FourierInvPair.fourier_fourierInv_eq g

end ConeSupport

namespace ConeSupport

/--
[fourier_smulLeftCLM_eq_schwartzConvolution](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma fourier_smulLeftCLM_eq_schwartzConvolution
  {n : ℕ}
  {μ : E n → ℂ}
  {v : 𝓢'(E n, ℂ)}
-- given
  (hμ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ)
  (hμc : HasCompactSupport μ) :
-- imply
  ∃ f : 𝓢(E n, ℂ), 𝓕 (TemperedDistribution.smulLeftCLM ℂ μ v) = schwartzConvolution (𝓕 v) f := by
-- proof
  let μ_s : 𝓢(E n, ℂ) := hμc.toSchwartzMap hμ
  use 𝓕 μ_s
  ext ψ
  simp only [TemperedDistribution.fourier_apply]
  show v (SchwartzMap.smulLeftCLM ℂ μ (𝓕 ψ)) =
    (𝓕 v) ((SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
      (schwartzReflectionCLM (𝓕 μ_s))) ψ)
  rw [TemperedDistribution.fourier_apply]
  congr 1
  rw [SchwartzMap.fourier_convolution, fourier_schwartzReflection_fourier]
  ext x
  have htg : Function.HasTemperateGrowth μ := hμc.hasTemperateGrowth hμ
  rw [SchwartzMap.pairing_apply, SchwartzMap.smulLeftCLM_apply htg]
  simp only [ContinuousLinearMap.mul_apply', smul_eq_mul]
  have : μ_s x = μ x := HasCompactSupport.toSchwartzMap_toFun hμc hμ x
  rw [this]

end ConeSupport

namespace ConeSupport

/--
[fourier_compact_cutoff_eq_schwartz_convolution](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma fourier_compact_cutoff_eq_schwartz_convolution
  {n : ℕ}
  {u : 𝓢'(E n, ℂ)}
  {φ φ' : E n → ℂ}
-- given
  (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
  (hφc : HasCompactSupport φ)
  (hφ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ')
  (hφ'c : HasCompactSupport φ')
  (hsup : tsupport φ' ⊆ Function.support φ) :
-- imply
  ∃ f : 𝓢(E n, ℂ), 𝓕 (TemperedDistribution.smulLeftCLM ℂ φ' u) = schwartzConvolution (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ u)) f := by
-- proof
  obtain ⟨μ, hμ_smooth, hμ_compact, hfactor⟩ :=
    smooth_factorization_smulLeftCLM u φ φ' hφ hφc hφ' hφ'c hsup
  obtain ⟨f, hconv⟩ :=
    fourier_smulLeftCLM_eq_schwartzConvolution μ hμ_smooth hμ_compact
      (TemperedDistribution.smulLeftCLM ℂ φ u)
  exact ⟨f, by rw [hfactor, hconv]⟩

end ConeSupport

namespace ConeSupport

/--
[cssSphere_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma cssSphere_isClosed
  {n : ℕ}
  {u : 𝓢'(E n, ℂ)} :
-- imply
  IsClosed (ConicSingularSupportSphere u) := by
-- proof
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro ω hω
  simp only [Set.mem_compl_iff, ConicSingularSupportSphere, Set.mem_setOf_eq, not_not] at hω
  obtain ⟨g, ⟨hg_smooth, R, hR, hR_lt, R₀, hR₀, hg_supp, ψ, hψ_hom, hψ_ne, hg_eq⟩, f, hf⟩ := hω
  have hR1 : (0 : ℝ) < R + 1 := by linarith
  set φ : Sphere n → ℂ := fun ω' => g ((R + 1) • (↑ω' : E n)) with hφ_def
  have hφ_cont : Continuous φ :=
    hg_smooth.continuous.comp (continuous_const.smul continuous_subtype_val)
  have hφ_eq : ∀ ω' : Sphere n, ψ (↑ω' : E n) = φ ω' := by
    intro ω'
    have h_sphere : ‖(↑ω' : E n)‖ = 1 := by
      have := ω'.2; simp only [Metric.mem_sphere, dist_zero_right] at this; exact this
    have h_norm : R < ‖(R + 1) • (↑ω' : E n)‖ := by
      rw [norm_smul, Real.norm_of_nonneg hR1.le, h_sphere, mul_one]; linarith
    have h_ne : (↑ω' : E n) ≠ 0 := by
      intro h; rw [h, norm_zero] at h_sphere; exact zero_ne_one h_sphere
    rw [← hψ_hom (R + 1) hR1 (↑ω') h_ne, ← hg_eq _ h_norm]
  refine ⟨φ ⁻¹' {(0 : ℂ)}ᶜ, ?_, hφ_cont.isOpen_preimage _ isOpen_compl_singleton, ?_⟩
  · intro ω' hω'
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hω'
    simp only [Set.mem_compl_iff, ConicSingularSupportSphere, Set.mem_setOf_eq, not_not]
    exact ⟨g, ⟨hg_smooth, R, hR, hR_lt, R₀, hR₀, hg_supp, ψ, hψ_hom, (hφ_eq ω') ▸ hω', hg_eq⟩, f, hf⟩
  · simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    rwa [← hφ_eq]

end ConeSupport

namespace ConeSupport

/--
[coneSupportSphere_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma coneSupportSphere_isClosed
  {n : ℕ}
  {u : 𝓢'(E n, ℂ)} :
-- imply
  IsClosed (ConeSupportSphere u) := by
-- proof
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro ω hω
  simp only [Set.mem_compl_iff, ConeSupportSphere, Set.mem_setOf_eq, not_not] at hω
  obtain ⟨g, ⟨hg_smooth, R, hR, hR_lt, R₀, hR₀, hg_supp, ψ, hψ_hom, hψ_ne, hg_eq⟩, hgu⟩ := hω
  have hR1 : (0 : ℝ) < R + 1 := by linarith
  set φ : Sphere n → ℂ := fun ω' => g ((R + 1) • (↑ω' : E n)) with hφ_def
  have hφ_cont : Continuous φ :=
    hg_smooth.continuous.comp (continuous_const.smul continuous_subtype_val)
  have hφ_eq : ∀ ω' : Sphere n, ψ (↑ω' : E n) = φ ω' := by
    intro ω'
    have h_sphere : ‖(↑ω' : E n)‖ = 1 := by
      have := ω'.2; simp only [Metric.mem_sphere, dist_zero_right] at this; exact this
    have h_norm : R < ‖(R + 1) • (↑ω' : E n)‖ := by
      rw [norm_smul, Real.norm_of_nonneg hR1.le, h_sphere, mul_one]; linarith
    have h_ne : (↑ω' : E n) ≠ 0 := by
      intro h; rw [h, norm_zero] at h_sphere; exact zero_ne_one h_sphere
    rw [← hψ_hom (R + 1) hR1 (↑ω') h_ne, ← hg_eq _ h_norm]
  refine ⟨φ ⁻¹' {(0 : ℂ)}ᶜ, ?_, hφ_cont.isOpen_preimage _ isOpen_compl_singleton, ?_⟩
  · intro ω' hω'
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hω'
    simp only [Set.mem_compl_iff, ConeSupportSphere, Set.mem_setOf_eq, not_not]
    exact ⟨g, ⟨hg_smooth, R, hR, hR_lt, R₀, hR₀, hg_supp, ψ, hψ_hom, (hφ_eq ω') ▸ hω', hg_eq⟩, hgu⟩
  · simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    rwa [← hφ_eq]

end ConeSupport

namespace ConeSupport

/--
[contDiff_isOpen_support](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma contDiff_isOpen_support
  {n : ℕ}
  {φ : E n → ℂ}
-- given
  (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) :
-- imply
  IsOpen (Function.support φ) :=
-- proof
  hφ.continuous.isOpen_support

end ConeSupport

namespace ConeSupport

/--
[parseval_temperate_growth_schwartz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma parseval_temperate_growth_schwartz
  {n : ℕ}
  {g : E n → ℂ}
  {ω : Sphere n}
-- given
  (hg : IsConicCutoffNear g ω) :
-- imply
  ∃ (F : E n → ℂ), Function.HasTemperateGrowth F ∧ ∀ (h : 𝓢(E n, ℂ)), ∫ x, g x • (𝓕 h) x = ∫ x, h x • F x := by
-- proof
  have hg_tg : Function.HasTemperateGrowth g := isConicCutoffNear_hasTemperateGrowth g ω hg
  have hg_neg_tg : Function.HasTemperateGrowth (g ∘ Neg.neg) := hasTemperateGrowth_comp_neg hg_tg
  obtain ⟨G, hG_tg, hG_eq⟩ := DifferentialOperators.temperateGrowth_inverseFT_exists
    (g ∘ Neg.neg) hg_neg_tg
  refine ⟨G, hG_tg, fun h => ?_⟩
  rw [← hG_eq h]
  have hfi : ∀ x : E n, (𝓕⁻ h) x = (𝓕 h) (-x) := by
    intro x
    have heq := SchwartzMap.fourierInv_apply_eq h
    have : (𝓕⁻ h) x = ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv) (𝓕 h)) x := by
      rw [← heq]
    rw [this, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
    simp [LinearIsometryEquiv.neg]
  simp_rw [Function.comp_apply, hfi]
  exact (integral_neg_eq_self (fun ξ => g ξ • (𝓕 h) ξ) volume).symm

end ConeSupport

namespace ConeSupport

/--
[smulLeftCLM_schwartz_embed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma smulLeftCLM_schwartz_embed
  {n : ℕ}
  {μ : E n → ℂ}
  {f : SchwartzMap (E n) ℂ}
-- given
  (hμ : Function.HasTemperateGrowth μ) :
-- imply
  TemperedDistribution.smulLeftCLM ℂ μ (f : 𝓢'(E n, ℂ)) = ((SchwartzMap.smulLeftCLM ℂ μ f) : 𝓢'(E n, ℂ)) := by
-- proof
  ext ψ
  simp only [TemperedDistribution.smulLeftCLM_apply_apply,
    SchwartzMap.toTemperedDistributionCLM_apply_apply]
  congr 1; ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply hμ, SchwartzMap.smulLeftCLM_apply_apply hμ]
  simp only [smul_eq_mul]; ring

end ConeSupport

namespace ConeSupport

/--
[isSmoothNear_of_smooth_nonzero_smulLeftCLM_schwartz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma isSmoothNear_of_smooth_nonzero_smulLeftCLM_schwartz
  {n : ℕ}
  {u : 𝓢'(E n, ℂ)}
  {g' : E n → ℂ}
  {x : E n}
  {f : SchwartzMap (E n) ℂ}
-- given
  (hg'_smooth : Function.HasTemperateGrowth g')
  (hg'_nonzero : g' x ≠ 0)
  (hf : TemperedDistribution.smulLeftCLM ℂ g' u = (f : 𝓢'(E n, ℂ))) :
-- imply
  IsSmoothNear u x := by
-- proof
  let ψ_bump : ContDiffBump x := ⟨1, 2, one_pos, by norm_num⟩
  let ψ_cx : E n → ℂ := fun y => ↑((ψ_bump : E n → ℝ) y)
  have hψ_tg : Function.HasTemperateGrowth ψ_cx :=
    (ψ_bump.hasCompactSupport.comp_left Complex.ofReal_zero).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp ψ_bump.contDiff)
  refine ⟨g' * ψ_cx, ?_, ?_, ?_, ?_⟩
  ·
    exact hg'_smooth.1.mul (Complex.ofRealCLM.contDiff.comp ψ_bump.contDiff)
  ·
    exact HasCompactSupport.mul_left
      (ψ_bump.hasCompactSupport.comp_left Complex.ofReal_zero)
  ·
    show g' x * ψ_cx x ≠ 0
    apply mul_ne_zero hg'_nonzero
    rw [Complex.ofReal_ne_zero]
    exact (ψ_bump.one_of_mem_closedBall (Metric.mem_closedBall_self (le_of_lt one_pos))).symm ▸
      one_ne_zero
  ·
    rw [show TemperedDistribution.smulLeftCLM ℂ (g' * ψ_cx) u =
      TemperedDistribution.smulLeftCLM ℂ ψ_cx (TemperedDistribution.smulLeftCLM ℂ g' u) from
      (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hg'_smooth hψ_tg u).symm]
    rw [hf]
    exact ⟨SchwartzMap.smulLeftCLM ℂ ψ_cx f, smulLeftCLM_schwartz_embed hψ_tg f⟩

end ConeSupport

namespace ConeSupport

/--
[exists_conicCutoff_nonzero_at](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma exists_conicCutoff_nonzero_at
  {n : ℕ}
  {ω : Sphere n}
  {x : E n}
-- given
  (hx : x ≠ 0) :
-- imply
  ∃ (g' : E n → ℂ), IsConicCutoffNear g' ω ∧ g' x ≠ 0 := by
-- proof
  have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set m := min ‖x‖ 1 with hm_def
  have hm_pos : 0 < m := lt_min hx_norm_pos one_pos
  have hrIn_pos : 0 < m / 3 := by positivity
  have hrInOut : m / 3 < m * 2 / 3 := by linarith
  let χ : ContDiffBump (0 : E n) := ⟨m / 3, m * 2 / 3, hrIn_pos, hrInOut⟩
  have hR_lt_one : m * 2 / 3 < 1 := by
    have : m ≤ 1 := min_le_right _ _; linarith
  refine ⟨fun y => Complex.ofReal (1 - χ y),
    ⟨?_, m * 2 / 3, by positivity, hR_lt_one, m / 3, by positivity, ?_,
      fun _ => 1, ?_, ?_, ?_⟩, ?_⟩
  ·
    rw [contDiff_infty]
    intro k
    exact_mod_cast Complex.ofRealCLM.contDiff.comp (contDiff_const.sub χ.contDiff)
  ·
    intro y hy
    simp only [Function.mem_support] at hy
    simp only [Set.mem_setOf_eq]
    by_contra h
    simp only [not_le] at h
    have hy_ball : y ∈ Metric.closedBall (0 : E n) χ.rIn := by
      simp only [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt h
    have : χ y = 1 := χ.one_of_mem_closedBall hy_ball
    simp only [this, sub_self, Complex.ofReal_zero] at hy
    exact hy rfl
  ·
    intro a _ y _; rfl
  ·
    exact one_ne_zero
  ·
    intro y hy
    have hy_out : χ.rOut ≤ dist y 0 := by
      simp only [dist_zero_right]; exact le_of_lt hy
    have : χ y = 0 := χ.zero_of_le_dist hy_out
    simp only [this, sub_zero, Complex.ofReal_one]
  ·
    have hx_out : χ.rOut ≤ dist x 0 := by
      simp only [dist_zero_right]
      show m * 2 / 3 ≤ ‖x‖
      have : m ≤ ‖x‖ := min_le_left _ _
      linarith
    have : χ x = 0 := χ.zero_of_le_dist hx_out
    simp only [this, sub_zero, Complex.ofReal_one]
    exact one_ne_zero

end ConeSupport

namespace ConeSupport

/--
[conicCutoff_support_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma conicCutoff_support_isOpen
  {n : ℕ}
  {g : E n → ℂ}
  {ω : Sphere n}
-- given
  (hg : IsConicCutoffNear g ω) :
-- imply
  IsOpen (Function.support g) :=
-- proof
  hg.1.continuous.isOpen_support

end ConeSupport

namespace ConeSupport

/--
[conicCutoff_mem_support](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma conicCutoff_mem_support
  {n : ℕ}
  {g : E n → ℂ}
  {ω : Sphere n}
-- given
  (hg : IsConicCutoffNear g ω) :
-- imply
  (ω : E n) ∈ Function.support g := by
-- proof
  obtain ⟨_, R, hR_pos, hR_lt, R₀, _, _, ψ, hψ_hom, hψ_ne, hg_eq⟩ := hg
  have hω_norm : ‖(ω : E n)‖ = 1 := by
    have := ω.2; simp only [Metric.mem_sphere, dist_zero_right] at this; exact this
  have hR_lt_norm : R < ‖(ω : E n)‖ := by rw [hω_norm]; exact hR_lt
  rw [Function.mem_support]
  rwa [hg_eq _ hR_lt_norm]
/-- Neighbourhood formulation: if `ω₁` is not in `Css(𝓕(g₀ · u))`, there are
neighbourhoods `Ũ ∋ ω₀` and `V ∋ ω₁` such that for every conic cutoff `g'` near `ω₀` with
support in `Ũ`, `V` is disjoint from `Css(𝓕(g' · u))`. -/
end ConeSupport


namespace WavefrontSet

/--
[ClosedBall.norm_neg_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma ClosedBall.norm_neg_eq
  {n : ℕ}
  {p : ClosedBall n} :
-- imply
  ‖(-p).val‖ = ‖p.val‖ := by
-- proof
  rw [ClosedBall.neg_val, norm_neg]

end WavefrontSet

namespace WavefrontSet

/--
[notMem_dsupport_of_smulLeftCLM_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma notMem_dsupport_of_smulLeftCLM_eq_zero
  {n : ℕ}
  {n}
  {n : ℕ}
  {u : 𝓢'(ConeSupport.E n, ℂ)}
  {g : ConeSupport.E n → ℂ}
  {x : ConeSupport.E n}
-- given
  (hg : Function.HasTemperateGrowth g)
  (hg_ne : g x ≠ 0)
  (hgu : TemperedDistribution.smulLeftCLM ℂ g u = 0) :
-- imply
  x ∉ Distribution.dsupport u := by
-- proof
  rw [Distribution.notMem_dsupport_iff]
  have hg_cont : Continuous g := hg.1.continuous
  have hV_open : IsOpen {y | g y ≠ 0} := isOpen_ne_fun hg_cont continuous_const
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hV_open x hg_ne
  refine ⟨Metric.ball x r, ?_, Metric.isOpen_ball, Metric.mem_ball_self hr_pos⟩
  intro φ hφ_supp
  have hφ_compact : HasCompactSupport (⇑φ) :=
    (isCompact_closedBall x r).of_isClosed_subset (isClosed_tsupport _)
      (hφ_supp.trans Metric.ball_subset_closedBall)
  have hφ_g_ne : ∀ y ∈ tsupport (⇑φ), g y ≠ 0 := fun y hy => hr_sub (hφ_supp hy)
  set ψ_fun : ConeSupport.E n → ℂ := fun y => (g y)⁻¹ * φ y
  have hψ_compact : HasCompactSupport ψ_fun := by
    apply hφ_compact.mono
    intro y hy
    simp only [Function.mem_support, ne_eq] at hy ⊢
    intro hφ0; apply hy; show (g y)⁻¹ * φ y = 0; rw [hφ0, mul_zero]
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ_fun := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : g y ≠ 0
    · exact (hg.1.contDiffAt.inv hy).mul φ.smooth'.contDiffAt
    · simp only [ne_eq, not_not] at hy
      have hy_notin : y ∉ tsupport (⇑φ) := fun h => absurd hy (hφ_g_ne y h)
      have h_eq : ψ_fun =ᶠ[nhds y] fun _ => (0 : ℂ) := by
        have h1 := notMem_tsupport_iff_eventuallyEq.mp hy_notin
        filter_upwards [h1] with z hz
        show (g z)⁻¹ * φ z = 0
        have : φ z = 0 := by simpa using hz
        rw [this, mul_zero]
      exact contDiffAt_const.congr_of_eventuallyEq h_eq
  let ψ : 𝓢(ConeSupport.E n, ℂ) := hψ_compact.toSchwartzMap hψ_smooth
  have hgψ : SchwartzMap.smulLeftCLM ℂ g ψ = φ := by
    ext y
    simp only [SchwartzMap.smulLeftCLM_apply_apply hg]
    show g y • ((g y)⁻¹ * φ y) = φ y
    by_cases hy : g y = 0
    · have : φ y = 0 := by
      have h1 : y ∉ Function.support (⇑φ) := fun h' =>
        absurd hy (hφ_g_ne y (subset_tsupport _ h'))
      simpa [Function.mem_support] using h1
      simp [hy, this]
    · rw [smul_eq_mul]; field_simp
  calc u φ = u (SchwartzMap.smulLeftCLM ℂ g ψ) := by rw [hgψ]
    _ = (TemperedDistribution.smulLeftCLM ℂ g u) ψ :=
      TemperedDistribution.smulLeftCLM_apply_apply g u ψ
    _ = (0 : 𝓢'(ConeSupport.E n, ℂ)) ψ := by rw [hgu]
    _ = 0 := ContinuousLinearMap.zero_apply ψ

end WavefrontSet

namespace WavefrontSet

/--
[isClosed_csp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma isClosed_csp
  {n : ℕ}
  {n}
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  IsClosed (Csp u) := by
-- proof
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro p hp
  simp only [Set.mem_compl_iff, Csp, Set.mem_setOf_eq] at hp
  by_cases h : ‖p.val‖ = 1
  ·
    rw [dif_pos h] at hp
    simp only [ConeSupport.ConeSupportSphere, Set.mem_setOf_eq, not_not] at hp
    obtain ⟨g, hg_conic, hgu⟩ := hp
    have ⟨hg_smooth, R, hR, hR_lt, R₀, hR₀, hg_supp, ψ, hψ_hom, hψ_ne, hg_eq⟩ := hg_conic
    have hR1 : (0 : ℝ) < R + 1 := by linarith
    set G : ClosedBall n → ℂ := fun q => g ((R + 1) • q.val)
    have hG_cont : Continuous G :=
      hg_smooth.continuous.comp (continuous_const.smul continuous_subtype_val)
    have hNorm : IsOpen {q : ClosedBall n | R / (R + 1) < ‖q.val‖} := by
      have : {q : ClosedBall n | R / (R + 1) < ‖q.val‖} =
        Subtype.val ⁻¹' {v | R / (R + 1) < ‖v‖} := rfl
      rw [this]; exact isOpen_induced (isOpen_lt continuous_const continuous_norm)
    have hp_mem_norm : R / (R + 1) < ‖p.val‖ := by
      rw [h, div_lt_iff₀ hR1]; linarith
    set T := G ⁻¹' {(0 : ℂ)}ᶜ ∩ {q : ClosedBall n | R / (R + 1) < ‖q.val‖}
    refine ⟨T, ?_, (hG_cont.isOpen_preimage _ isOpen_compl_singleton).inter hNorm, ?_⟩
    ·
      intro q hq
      obtain ⟨hqG, hqN⟩ := hq
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hqG
      simp only [Set.mem_setOf_eq] at hqN
      simp only [Set.mem_compl_iff, Csp, Set.mem_setOf_eq]
      by_cases hq1 : ‖q.val‖ = 1
      ·
        rw [dif_pos hq1]
        simp only [ConeSupport.ConeSupportSphere, Set.mem_setOf_eq, not_not]
        have hq_ne : q.val ≠ 0 := by
          intro he; rw [he, norm_zero] at hq1; exact zero_ne_one hq1
        have : R < ‖(R + 1) • q.val‖ := by
          rw [norm_smul, Real.norm_of_nonneg hR1.le, hq1, mul_one]; linarith
        have hψq : ψ q.val ≠ 0 := by
          rwa [← hψ_hom (R+1) hR1 q.val hq_ne, ← hg_eq _ this]
        exact ⟨g, ⟨hg_smooth, R, hR, hR_lt, R₀, hR₀, hg_supp, ψ, hψ_hom, hψq, hg_eq⟩, hgu⟩
      ·
        rw [dif_neg hq1]
        have hq_lt : ‖q.val‖ < 1 := lt_of_le_of_ne q.property hq1
        have hq_ne : q.val ≠ 0 := by
          intro he; rw [he, norm_zero] at hqN; linarith [div_pos hR hR1]
        have h1sub : (0 : ℝ) < 1 - ‖q.val‖ := by linarith
        have htoEuc_norm : R < ‖q.toEuclidean hq_lt‖ := by
          unfold ClosedBall.toEuclidean
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr h1sub.le), inv_mul_eq_div]
          rw [lt_div_iff₀ h1sub]
          have := hqN; rw [div_lt_iff₀ hR1] at this
          linarith
        have hψ_toEuc : g (q.toEuclidean hq_lt) = ψ (q.toEuclidean hq_lt) :=
          hg_eq _ htoEuc_norm
        have hψ_hom_toEuc : ψ (q.toEuclidean hq_lt) = ψ q.val := by
          unfold ClosedBall.toEuclidean
          exact hψ_hom _ (inv_pos.mpr h1sub) q.val hq_ne
        have hG_eq : g ((R + 1) • q.val) = ψ q.val := by
          have : R < ‖(R + 1) • q.val‖ := by
            rw [norm_smul, Real.norm_of_nonneg hR1.le]
            calc R = R * 1 := (mul_one R).symm
              _ < (R + 1) * ‖q.val‖ := by
                have := hqN; rw [div_lt_iff₀ hR1] at this; linarith
          rw [hg_eq _ this, hψ_hom (R+1) hR1 q.val hq_ne]
        have hψq : ψ q.val ≠ 0 := by rwa [← hG_eq]
        have hg_ne : g (q.toEuclidean hq_lt) ≠ 0 := by rw [hψ_toEuc, hψ_hom_toEuc]; exact hψq
        exact notMem_dsupport_of_smulLeftCLM_eq_zero u g (q.toEuclidean hq_lt)
          (ConeSupport.isConicCutoffNear_hasTemperateGrowth g _ hg_conic) hg_ne hgu
    ·
      refine ⟨?_, hp_mem_norm⟩
      show g ((R + 1) • p.val) ≠ 0
      have : R < ‖(R + 1) • p.val‖ := by
        rw [norm_smul, Real.norm_of_nonneg hR1.le, h, mul_one]; linarith
      have hp_ne : p.val ≠ 0 := by intro he; rw [he, norm_zero] at h; exact zero_ne_one h
      rw [hg_eq _ this, hψ_hom (R+1) hR1 p.val hp_ne]; exact hψ_ne
  ·
    rw [dif_neg h] at hp
    have hp_lt : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h
    set S := (Distribution.dsupport (f := u))ᶜ
    have hp_mem_S : p.toEuclidean hp_lt ∈ S := hp
    set decompact : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
      fun v => (1 - ‖v‖)⁻¹ • v
    have hdecompact_cont : ContinuousOn decompact (Metric.ball 0 1) :=
      ((continuousOn_const.sub continuous_norm.continuousOn).inv₀
        (fun v hv => by
          simp only [Metric.mem_ball, dist_zero_right] at hv
          simp only [ne_eq, sub_eq_zero]; linarith)).smul continuousOn_id
    have hS_open : IsOpen S := (Distribution.isClosed_dsupport).isOpen_compl
    have hW_open : IsOpen (decompact ⁻¹' S ∩ Metric.ball 0 1) := by
      rw [Set.inter_comm]
      exact hdecompact_cont.isOpen_inter_preimage Metric.isOpen_ball hS_open
    have hp_in_W : p.val ∈ decompact ⁻¹' S ∩ Metric.ball 0 1 := by
      constructor
      · show decompact p.val ∈ S
        exact hp_mem_S
      · simp only [Metric.mem_ball, dist_zero_right]; exact hp_lt
    refine ⟨Subtype.val ⁻¹' (decompact ⁻¹' S ∩ Metric.ball 0 1), ?_,
      isOpen_induced hW_open, ?_⟩
    ·
      intro q hq
      simp only [Set.mem_preimage, Set.mem_inter_iff, Metric.mem_ball, dist_zero_right,
        Set.mem_compl_iff, Csp, Set.mem_setOf_eq] at hq ⊢
      obtain ⟨hqS, hq_lt⟩ := hq
      rwa [dif_neg (ne_of_lt hq_lt)]
    ·
      simp only [Set.mem_preimage]; exact hp_in_W

end WavefrontSet

namespace WavefrontSet

/--
[isClosed_css](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma isClosed_css
  {n : ℕ}
  {n}
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  IsClosed (Css u) := by
-- proof
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro p hp
  simp only [Set.mem_compl_iff, Css, Set.mem_setOf_eq] at hp
  by_cases h : ‖p.val‖ = 1
  ·
    rw [dif_pos h] at hp
    simp only [ConeSupport.ConicSingularSupportSphere, Set.mem_setOf_eq, not_not] at hp
    obtain ⟨g, hg_conic, f, hf⟩ := hp
    have ⟨hg_smooth, R, hR, hR_lt, R₀, hR₀, hg_supp, ψ, hψ_hom, hψ_ne, hg_eq⟩ := hg_conic
    have hR1 : (0 : ℝ) < R + 1 := by linarith
    set G : ClosedBall n → ℂ := fun q => g ((R + 1) • q.val)
    have hG_cont : Continuous G :=
      hg_smooth.continuous.comp (continuous_const.smul continuous_subtype_val)
    have hNorm : IsOpen {q : ClosedBall n | R / (R + 1) < ‖q.val‖} := by
      have : {q : ClosedBall n | R / (R + 1) < ‖q.val‖} =
        Subtype.val ⁻¹' {v | R / (R + 1) < ‖v‖} := rfl
      rw [this]; exact isOpen_induced (isOpen_lt continuous_const continuous_norm)
    have hp_mem_norm : R / (R + 1) < ‖p.val‖ := by
      rw [h, div_lt_iff₀ hR1]; linarith
    set T := G ⁻¹' {(0 : ℂ)}ᶜ ∩ {q : ClosedBall n | R / (R + 1) < ‖q.val‖}
    refine ⟨T, ?_, (hG_cont.isOpen_preimage _ isOpen_compl_singleton).inter hNorm, ?_⟩
    ·
      intro q hq
      obtain ⟨hqG, hqN⟩ := hq
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hqG
      simp only [Set.mem_setOf_eq] at hqN
      simp only [Set.mem_compl_iff, Css, Set.mem_setOf_eq]
      by_cases hq1 : ‖q.val‖ = 1
      ·
        rw [dif_pos hq1]
        simp only [ConeSupport.ConicSingularSupportSphere, Set.mem_setOf_eq, not_not]
        have hq_ne : q.val ≠ 0 := by
          intro he; rw [he, norm_zero] at hq1; exact zero_ne_one hq1
        have : R < ‖(R + 1) • q.val‖ := by
          rw [norm_smul, Real.norm_of_nonneg hR1.le, hq1, mul_one]; linarith
        have hψq : ψ q.val ≠ 0 := by
          rwa [← hψ_hom (R+1) hR1 q.val hq_ne, ← hg_eq _ this]
        exact ⟨g, ⟨hg_smooth, R, hR, hR_lt, R₀, hR₀, hg_supp, ψ, hψ_hom, hψq, hg_eq⟩, f, hf⟩
      ·
        rw [dif_neg hq1]
        have hq_lt : ‖q.val‖ < 1 := lt_of_le_of_ne q.property hq1
        simp only [ConeSupport.singularSupport, Set.mem_setOf_eq, not_not]
        have hq_ne : q.val ≠ 0 := by
          intro he; rw [he, norm_zero] at hqN; linarith [div_pos hR hR1]
        have h1sub : (0 : ℝ) < 1 - ‖q.val‖ := by linarith
        have htoEuc_norm : R < ‖q.toEuclidean hq_lt‖ := by
          unfold ClosedBall.toEuclidean
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr h1sub.le), inv_mul_eq_div]
          rw [lt_div_iff₀ h1sub]
          have := hqN; rw [div_lt_iff₀ hR1] at this
          linarith
        have hψ_toEuc : g (q.toEuclidean hq_lt) = ψ (q.toEuclidean hq_lt) :=
          hg_eq _ htoEuc_norm
        have hψ_hom_toEuc : ψ (q.toEuclidean hq_lt) = ψ q.val := by
          unfold ClosedBall.toEuclidean
          exact hψ_hom _ (inv_pos.mpr h1sub) q.val hq_ne
        have hG_eq : g ((R + 1) • q.val) = ψ q.val := by
          have : R < ‖(R + 1) • q.val‖ := by
            rw [norm_smul, Real.norm_of_nonneg hR1.le]
            calc R = R * 1 := (mul_one R).symm
              _ < (R + 1) * ‖q.val‖ := by
                have := hqN; rw [div_lt_iff₀ hR1] at this; linarith
          rw [hg_eq _ this, hψ_hom (R+1) hR1 q.val hq_ne]
        have hψq : ψ q.val ≠ 0 := by rwa [← hG_eq]
        have hg_ne : g (q.toEuclidean hq_lt) ≠ 0 := by rw [hψ_toEuc, hψ_hom_toEuc]; exact hψq
        exact ConeSupport.isSmoothNear_of_smooth_nonzero_smulLeftCLM_schwartz u g
          (q.toEuclidean hq_lt)
          (ConeSupport.isConicCutoffNear_hasTemperateGrowth g _ hg_conic) hg_ne f hf
    ·
      refine ⟨?_, hp_mem_norm⟩
      show g ((R + 1) • p.val) ≠ 0
      have : R < ‖(R + 1) • p.val‖ := by
        rw [norm_smul, Real.norm_of_nonneg hR1.le, h, mul_one]; linarith
      have hp_ne : p.val ≠ 0 := by intro he; rw [he, norm_zero] at h; exact zero_ne_one h
      rw [hg_eq _ this, hψ_hom (R+1) hR1 p.val hp_ne]; exact hψ_ne
  ·
    rw [dif_neg h] at hp
    simp only [ConeSupport.singularSupport, Set.mem_setOf_eq, not_not] at hp
    obtain ⟨φ, hφ_smooth, hφ_compact, hφ_ne, f, hf⟩ := hp
    have hp_lt : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h
    set Ψ : EuclideanSpace ℝ (Fin n) → ℂ :=
      fun v => if hv : ‖v‖ < 1 then φ ((1 - ‖v‖)⁻¹ • v) else 0
    have hΨp : Ψ p.val ≠ 0 := by simp only [Ψ, dif_pos hp_lt]; exact hφ_ne
    have hΨ_supp : Function.support Ψ ⊆ {v | ‖v‖ < 1} := by
      intro v hv; simp only [Function.mem_support, Ψ] at hv
      by_contra h_ge; simp only [Set.mem_setOf_eq, not_lt] at h_ge
      exact hv (dif_neg (not_lt.mpr h_ge))
    have hΨ_open : IsOpen (Function.support Ψ) := by
      suffices h : Function.support Ψ =
        (fun v => φ ((1 - ‖v‖)⁻¹ • v)) ⁻¹' {(0 : ℂ)}ᶜ ∩ Metric.ball 0 1 by
        rw [h]
        have hcont : ContinuousOn (fun v => φ ((1 - ‖v‖)⁻¹ • v)) (Metric.ball 0 1) :=
          hφ_smooth.continuous.comp_continuousOn
            (((continuousOn_const.sub continuous_norm.continuousOn).inv₀
              (fun v hv => by
                simp only [Metric.mem_ball, dist_zero_right] at hv
                simp only [ne_eq, sub_eq_zero]; linarith)).smul continuousOn_id)
        rw [Set.inter_comm]
        exact hcont.isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton
      ext v
      simp only [Function.mem_support, Ψ, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_compl_iff, Set.mem_singleton_iff, Metric.mem_ball, dist_zero_right]
      constructor
      · intro hv
        have hvlt : ‖v‖ < 1 := by
          by_contra hge; simp only [not_lt] at hge
          exact hv (dif_neg (not_lt.mpr hge))
        exact ⟨by rwa [dif_pos hvlt] at hv, hvlt⟩
      · rintro ⟨hvne, hvlt⟩; rwa [dif_pos hvlt]
    refine ⟨Subtype.val ⁻¹' (Function.support Ψ), ?_, isOpen_induced hΨ_open, ?_⟩
    ·
      intro q hq
      simp only [Set.mem_preimage, Function.mem_support, Set.mem_compl_iff, Css,
        Set.mem_setOf_eq] at hq ⊢
      have hq_lt : ‖q.val‖ < 1 := hΨ_supp (Function.mem_support.mpr hq)
      rw [dif_neg (ne_of_lt hq_lt)]
      simp only [ConeSupport.singularSupport, Set.mem_setOf_eq, not_not]
      simp only [Ψ, dif_pos hq_lt] at hq
      exact ⟨φ, hφ_smooth, hφ_compact, hq, f, hf⟩
    ·
      simp only [Set.mem_preimage, Function.mem_support]; exact hΨp

end WavefrontSet

namespace WavefrontSet

/--
[css_subadditive_not_mem'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma css_subadditive_not_mem'
  {n : ℕ}
  {n}
  {n : ℕ}
  {u₁ u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {p : ClosedBall n}
-- given
  (h₁ : p ∉ Css u₁)
  (h₂ : p ∉ Css u₂) :
-- imply
  p ∉ Css (u₁ + u₂) := by
-- proof
  simp only [Css, Set.mem_setOf] at h₁ h₂ ⊢
  split_ifs with h
  ·
    rw [dif_pos h] at h₁ h₂
    simp only [ConeSupport.ConicSingularSupportSphere, Set.mem_setOf, not_not] at h₁ h₂ ⊢
    obtain ⟨g₁, hg₁_conic, f₁, hf₁⟩ := h₁
    obtain ⟨g₂, hg₂_conic, f₂, hf₂⟩ := h₂
    refine ⟨g₁ * g₂, ?_, ?_⟩
    ·
      obtain ⟨hg₁_smooth, R₁, hR₁, hR₁_lt, R₀₁, hR₀₁, hg₁_supp, ψ₁, hψ₁_hom, hψ₁_ne, hg₁_eq⟩ := hg₁_conic
      obtain ⟨hg₂_smooth, R₂, hR₂, hR₂_lt, R₀₂, hR₀₂, hg₂_supp, ψ₂, hψ₂_hom, hψ₂_ne, hg₂_eq⟩ := hg₂_conic
      refine ⟨hg₁_smooth.mul hg₂_smooth, max R₁ R₂, lt_max_of_lt_left hR₁,
        max_lt hR₁_lt hR₂_lt,
        max R₀₁ R₀₂, lt_max_of_lt_left hR₀₁, ?_, ψ₁ * ψ₂, ?_, ?_, ?_⟩
      ·
        intro x hx
        simp only [Set.mem_setOf]
        rw [Function.mem_support, Pi.mul_apply] at hx
        have hx_ne : g₁ x ≠ 0 ∧ g₂ x ≠ 0 := mul_ne_zero_iff.mp hx
        have h1 : x ∈ Function.support g₁ := Function.mem_support.mpr hx_ne.1
        have h2 : x ∈ Function.support g₂ := Function.mem_support.mpr hx_ne.2
        exact max_le (hg₁_supp h1) (hg₂_supp h2)
      ·
        intro a ha x hx
        simp only [Pi.mul_apply]
        rw [hψ₁_hom a ha x hx, hψ₂_hom a ha x hx]
      ·
        simp only [Pi.mul_apply]
        exact mul_ne_zero hψ₁_ne hψ₂_ne
      ·
        intro x hx
        simp only [Pi.mul_apply]
        rw [hg₁_eq x (lt_of_le_of_lt (le_max_left _ _) hx),
          hg₂_eq x (lt_of_le_of_lt (le_max_right _ _) hx)]
    ·
      have hg₁_tg : Function.HasTemperateGrowth g₁ :=
        ConeSupport.isConicCutoffNear_hasTemperateGrowth g₁ _ hg₁_conic
      have hg₂_tg : Function.HasTemperateGrowth g₂ :=
        ConeSupport.isConicCutoffNear_hasTemperateGrowth g₂ _ hg₂_conic
      have eq1 : TemperedDistribution.smulLeftCLM ℂ (g₁ * g₂) u₁ =
        TemperedDistribution.smulLeftCLM ℂ g₂ (TemperedDistribution.smulLeftCLM ℂ g₁ u₁) :=
        (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hg₁_tg hg₂_tg u₁).symm
      have mul_comm_g : g₂ * g₁ = g₁ * g₂ := mul_comm g₂ g₁
      have eq2 : TemperedDistribution.smulLeftCLM ℂ (g₁ * g₂) u₂ =
        TemperedDistribution.smulLeftCLM ℂ g₁ (TemperedDistribution.smulLeftCLM ℂ g₂ u₂) := by
        rw [← mul_comm_g]
        exact (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hg₂_tg hg₁_tg u₂).symm
      rw [show TemperedDistribution.smulLeftCLM ℂ (g₁ * g₂) (u₁ + u₂) =
        TemperedDistribution.smulLeftCLM ℂ (g₁ * g₂) u₁ +
        TemperedDistribution.smulLeftCLM ℂ (g₁ * g₂) u₂ from
        map_add (TemperedDistribution.smulLeftCLM ℂ (g₁ * g₂)) u₁ u₂]
      rw [eq1, hf₁, eq2, hf₂]
      rw [ConeSupport.smulLeftCLM_schwartz_embed hg₂_tg f₁]
      rw [ConeSupport.smulLeftCLM_schwartz_embed hg₁_tg f₂]
      exact ⟨SchwartzMap.smulLeftCLM ℂ g₂ f₁ + SchwartzMap.smulLeftCLM ℂ g₁ f₂,
        (map_add (SchwartzMap.toTemperedDistributionCLM _ ℂ _) _ _).symm⟩
  ·
    rw [dif_neg h] at h₁ h₂
    simp only [ConeSupport.singularSupport, Set.mem_setOf, not_not] at h₁ h₂ ⊢
    have hp : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h
    obtain ⟨φ₁, hφ₁_smooth, hφ₁_supp, hφ₁_ne, f₁, hf₁⟩ := h₁
    obtain ⟨φ₂, hφ₂_smooth, hφ₂_supp, hφ₂_ne, f₂, hf₂⟩ := h₂
    have hφ₁_tg : Function.HasTemperateGrowth φ₁ := hφ₁_supp.hasTemperateGrowth hφ₁_smooth
    have hφ₂_tg : Function.HasTemperateGrowth φ₂ := hφ₂_supp.hasTemperateGrowth hφ₂_smooth
    refine ⟨φ₁ * φ₂, hφ₁_smooth.mul hφ₂_smooth, hφ₁_supp.mul_right, ?_, ?_⟩
    ·
      simp only [Pi.mul_apply]
      exact mul_ne_zero hφ₁_ne hφ₂_ne
    ·
      have eq1 : TemperedDistribution.smulLeftCLM ℂ (φ₁ * φ₂) u₁ =
        TemperedDistribution.smulLeftCLM ℂ φ₂ (TemperedDistribution.smulLeftCLM ℂ φ₁ u₁) :=
        (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hφ₁_tg hφ₂_tg u₁).symm
      have eq2 : TemperedDistribution.smulLeftCLM ℂ (φ₁ * φ₂) u₂ =
        TemperedDistribution.smulLeftCLM ℂ φ₁ (TemperedDistribution.smulLeftCLM ℂ φ₂ u₂) := by
        rw [← mul_comm φ₂ φ₁]
        exact (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hφ₂_tg hφ₁_tg u₂).symm
      rw [ConeSupport.smulLeftCLM_add_right]
      rw [eq1, hf₁, eq2, hf₂]
      rw [ConeSupport.smulLeftCLM_schwartz_embed hφ₂_tg f₁]
      rw [ConeSupport.smulLeftCLM_schwartz_embed hφ₁_tg f₂]
      exact ⟨SchwartzMap.smulLeftCLM ℂ φ₂ f₁ + SchwartzMap.smulLeftCLM ℂ φ₁ f₂,
        (map_add (SchwartzMap.toTemperedDistributionCLM _ ℂ _) _ _).symm⟩

end WavefrontSet

namespace WavefrontSet

/--
[not_mem_css_schwartz'_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma not_mem_css_schwartz'_aux
  {n : ℕ}
  {n}
  {n : ℕ}
  {f : SchwartzMap (ConeSupport.E n) ℂ}
  {p : ClosedBall n} :
-- imply
  p ∉ Css (ConeSupport.schwEmbed f) := by
-- proof
  simp only [Css, Set.mem_setOf]
  split_ifs with h
  ·
    simp only [ConeSupport.ConicSingularSupportSphere, Set.mem_setOf, not_not]
    obtain ⟨g, hg⟩ := ConeSupport.exists_conicCutoff (p.toSphere h)
    exact ⟨g, hg, SchwartzMap.smulLeftCLM ℂ g f,
      ConeSupport.smulLeftCLM_schwEmbed_eq_local g f⟩
  ·
    simp only [ConeSupport.singularSupport, Set.mem_setOf, not_not]
    have hp : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h
    let c := p.toEuclidean hp
    let b : ContDiffBump c := ⟨1, 2, one_pos, by norm_num⟩
    refine ⟨fun x => Complex.ofReal (b x), ?_, ?_, ?_,
      SchwartzMap.smulLeftCLM ℂ (fun x => Complex.ofReal (b x)) f,
      ConeSupport.smulLeftCLM_schwEmbed_eq_local _ f⟩
    · rw [contDiff_infty]; intro k
      exact_mod_cast Complex.ofRealCLM.contDiff.comp b.contDiff
    · exact b.hasCompactSupport.comp_left Complex.ofReal_zero
    · have hcenter : b.toFun (p.toEuclidean hp) = 1 :=
      b.one_of_mem_closedBall (Metric.mem_closedBall_self (le_of_lt one_pos))
      simp [hcenter]

end WavefrontSet

namespace WavefrontSet

/--
[not_mem_css_schwartz'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma not_mem_css_schwartz'
  {n : ℕ}
  {n}
  {n : ℕ}
  {f : SchwartzMap (ConeSupport.E n) ℂ}
  {p : ClosedBall n} :
-- imply
  p ∉ Css (ConeSupport.schwEmbed f) := by
-- proof
  simp only [Css, Set.mem_setOf]
  split_ifs with h
  ·
    simp only [ConeSupport.ConicSingularSupportSphere, Set.mem_setOf, not_not]
    obtain ⟨g, hg⟩ := ConeSupport.exists_conicCutoff (p.toSphere h)
    exact ⟨g, hg, SchwartzMap.smulLeftCLM ℂ g f,
      ConeSupport.smulLeftCLM_schwEmbed_eq_local g f⟩
  ·
    simp only [ConeSupport.singularSupport, Set.mem_setOf, not_not]
    have hp : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h
    let c := p.toEuclidean hp
    let b : ContDiffBump c := ⟨1, 2, one_pos, by norm_num⟩
    refine ⟨fun x => Complex.ofReal (b x), ?_, ?_, ?_,
      SchwartzMap.smulLeftCLM ℂ (fun x => Complex.ofReal (b x)) f,
      ConeSupport.smulLeftCLM_schwEmbed_eq_local _ f⟩
    · rw [contDiff_infty]; intro k
      exact_mod_cast Complex.ofRealCLM.contDiff.comp b.contDiff
    · exact b.hasCompactSupport.comp_left Complex.ofReal_zero
    · have hcenter : b.toFun (p.toEuclidean hp) = 1 :=
      b.one_of_mem_closedBall (Metric.mem_closedBall_self (le_of_lt one_pos))
      simp [hcenter]

end WavefrontSet

namespace WavefrontSet

/--
[not_mem_wfsc_of_not_mem_css](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma not_mem_wfsc_of_not_mem_css
  {n : ℕ}
  {n}
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {p q : ClosedBall n}
-- given
  (_hpq : (p, q) ∈ BoundaryProd n)
  (hp : p ∉ Css u) :
-- imply
  (p, q) ∉ WFsc u := by
-- proof
  simp only [WFsc, Set.mem_setOf_eq, not_not]
  simp only [Css, Set.mem_setOf] at hp
  by_cases h : ‖p.val‖ = 1
  ·
    rw [dif_pos h]
    rw [dif_pos h] at hp
    simp only [ConeSupport.ConicSingularSupportSphere, Set.mem_setOf, not_not] at hp
    obtain ⟨g, hg, f, hf⟩ := hp
    refine ⟨g, hg, ?_⟩
    rw [hf, TemperedDistribution.fourier_toTemperedDistributionCLM_eq]
    exact not_mem_css_schwartz' (𝓕 f) q
  ·
    rw [dif_neg h]
    have hp_lt : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h
    rw [dif_neg h] at hp
    simp only [ConeSupport.singularSupport, Set.mem_setOf, not_not] at hp
    obtain ⟨φ, hφ_smooth, hφ_compact, hφ_ne, f, hf⟩ := hp
    refine ⟨φ, hφ_smooth, hφ_compact, hφ_ne, ?_⟩
    rw [hf, TemperedDistribution.fourier_toTemperedDistributionCLM_eq]
    exact not_mem_css_schwartz' (𝓕 f) q

end WavefrontSet

namespace WavefrontSet

/--
[not_mem_css_zero'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma not_mem_css_zero'
  {n : ℕ}
  {n}
  {n : ℕ}
  {p : ClosedBall n} :
-- imply
  p ∉ Css (0 : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) := by
-- proof
  simp only [Css, Set.mem_setOf]
  split_ifs with h
  ·
    simp only [ConeSupport.ConicSingularSupportSphere, Set.mem_setOf, not_not]
    obtain ⟨g, hg⟩ := ConeSupport.exists_conicCutoff (p.toSphere h)
    exact ⟨g, hg, 0, by simp [map_zero]⟩
  ·
    simp only [ConeSupport.singularSupport, Set.mem_setOf, not_not]
    have hp : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h
    let c := p.toEuclidean hp
    let b : ContDiffBump c := ⟨1, 2, one_pos, by norm_num⟩
    refine ⟨fun x => Complex.ofReal (b x), ?_, ?_, ?_, 0, by simp [map_zero]⟩
    · rw [contDiff_infty]; intro k
      exact_mod_cast Complex.ofRealCLM.contDiff.comp b.contDiff
    · exact b.hasCompactSupport.comp_left Complex.ofReal_zero
    · have hcenter : b.toFun (p.toEuclidean hp) = 1 :=
      b.one_of_mem_closedBall (Metric.mem_closedBall_self (le_of_lt one_pos))
      simp [hcenter]

end WavefrontSet

namespace WavefrontSet

/--
[schwartz_doubleFourier_eq_compNeg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma schwartz_doubleFourier_eq_compNeg
  {n : ℕ}
  {n}
  {φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  𝓕 (𝓕 φ) = ConeSupport.schwartzReflectionCLM φ := by
-- proof
  show 𝓕 (𝓕 φ) = (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.neg (R := ℝ) (M := EuclideanSpace ℝ (Fin n)))) φ
  have negCLE_eq : (LinearIsometryEquiv.neg ℝ (E := EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv =
    ContinuousLinearEquiv.neg ℝ := by ext x; simp
  have key : φ = (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv) (𝓕 (𝓕 φ)) := by
    rw [← SchwartzMap.fourierInv_apply_eq (𝓕 φ)]
    exact (FourierTransform.fourierInv_fourier_eq φ).symm
  have negNeg : ∀ g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (LinearIsometryEquiv.neg ℝ (E := EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv)
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (LinearIsometryEquiv.neg ℝ (E := EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv) g) = g := by
    intro g; ext x; simp [SchwartzMap.compCLMOfContinuousLinearEquiv]
  have step := congr_arg (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv) key
  rw [negNeg] at step
  rwa [negCLE_eq] at step

end WavefrontSet

namespace WavefrontSet

/--
[doubleFourier_eq_reflection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma doubleFourier_eq_reflection
  {n : ℕ}
  {n}
  {u : TemperedDistribution (ConeSupport.E n) ℂ} :
-- imply
  𝓕 (𝓕 u) = ConeSupport.reflection u := by
-- proof
  ext φ
  simp only [TemperedDistribution.fourier_apply]
  show u (𝓕 (𝓕 φ)) = (u.comp ConeSupport.schwartzReflectionCLM) φ
  simp only [ContinuousLinearMap.comp_apply]
  congr 1
  exact schwartz_doubleFourier_eq_compNeg φ

end WavefrontSet

namespace WavefrontSet

/--
[singularSupport_reflection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma singularSupport_reflection
  {n : ℕ}
  {n}
  {v : TemperedDistribution (ConeSupport.E n) ℂ}
  {x : ConeSupport.E n} :
-- imply
  x ∈ ConeSupport.singularSupport (ConeSupport.reflection v) ↔ (-x) ∈ ConeSupport.singularSupport v := by
-- proof
  simp only [ConeSupport.singularSupport, mem_setOf_eq]
  constructor
  ·
    intro hx hcontra
    apply hx
    obtain ⟨φ, hsmooth, hcompact, hne, f, hf⟩ := hcontra
    refine ⟨φ ∘ Neg.neg,
      hsmooth.comp (ContinuousLinearEquiv.neg ℝ).contDiff,
      hcompact.comp_homeomorph (Homeomorph.neg (ConeSupport.E n)),
      by simp [Function.comp_apply, hne], ?_⟩
    have key : TemperedDistribution.smulLeftCLM ℂ (φ ∘ Neg.neg) (ConeSupport.reflection v) =
      (TemperedDistribution.smulLeftCLM ℂ ((φ ∘ Neg.neg) ∘ Neg.neg) v).comp
        ConeSupport.schwartzReflectionCLM := by
      ext ψ
      show v (ConeSupport.schwartzReflectionCLM ((SchwartzMap.smulLeftCLM ℂ (φ ∘ Neg.neg)) ψ)) =
        v ((SchwartzMap.smulLeftCLM ℂ ((φ ∘ Neg.neg) ∘ Neg.neg)) (ConeSupport.schwartzReflectionCLM ψ))
      congr 1
      ext y
      simp only [ConeSupport.schwartzReflectionCLM, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
        Function.comp, ContinuousLinearEquiv.coe_neg, SchwartzMap.smulLeftCLM]
      split_ifs with h1 h2 h2
      · simp only [SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.lsmul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
        Function.comp, ContinuousLinearEquiv.coe_neg]
        simp [Pi.neg_apply, id]
      · exact absurd (ConeSupport.hasTemperateGrowth_comp_neg h1) h2
      · exact absurd (ConeSupport.hasTemperateGrowth_neg_iff.mpr h2) h1
      · simp
    have hgg : (φ ∘ Neg.neg) ∘ Neg.neg = φ := by ext; simp
    rw [key, hgg, hf]
    exact ⟨ConeSupport.schwartzReflectionCLM f, ConeSupport.reflection_schwartz_coercion f⟩
  ·
    intro hx hcontra
    apply hx
    obtain ⟨φ, hsmooth, hcompact, hne, f, hf⟩ := hcontra
    refine ⟨φ ∘ Neg.neg,
      hsmooth.comp (ContinuousLinearEquiv.neg ℝ).contDiff,
      hcompact.comp_homeomorph (Homeomorph.neg (ConeSupport.E n)),
      by simp [Function.comp_apply, hne], ?_⟩
    have key : TemperedDistribution.smulLeftCLM ℂ φ (ConeSupport.reflection v) =
      (TemperedDistribution.smulLeftCLM ℂ (φ ∘ Neg.neg) v).comp
        ConeSupport.schwartzReflectionCLM := by
      ext ψ
      show v (ConeSupport.schwartzReflectionCLM ((SchwartzMap.smulLeftCLM ℂ φ) ψ)) =
        v ((SchwartzMap.smulLeftCLM ℂ (φ ∘ Neg.neg)) (ConeSupport.schwartzReflectionCLM ψ))
      congr 1
      ext y
      simp only [ConeSupport.schwartzReflectionCLM, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
        Function.comp, ContinuousLinearEquiv.coe_neg, SchwartzMap.smulLeftCLM]
      split_ifs with h1 h2 h2
      · simp only [SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.lsmul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
        Function.comp, ContinuousLinearEquiv.coe_neg]
        simp [Pi.neg_apply, id]
      · exact absurd (ConeSupport.hasTemperateGrowth_comp_neg h1) h2
      · exact absurd (ConeSupport.hasTemperateGrowth_neg_iff.mpr h2) h1
      · simp
    have h1 : ConeSupport.reflection (TemperedDistribution.smulLeftCLM ℂ (φ ∘ Neg.neg) v) = ↑f := by
      show (TemperedDistribution.smulLeftCLM ℂ (φ ∘ Neg.neg) v).comp
        ConeSupport.schwartzReflectionCLM = (f : 𝓢'(ConeSupport.E n, ℂ))
      rwa [← key]
    have h2 : TemperedDistribution.smulLeftCLM ℂ (φ ∘ Neg.neg) v =
      ConeSupport.reflection (↑f) := by
      have h3 := congr_arg ConeSupport.reflection h1
      rwa [ConeSupport.reflection_reflection] at h3
    rw [h2]
    exact ⟨ConeSupport.schwartzReflectionCLM f, ConeSupport.reflection_schwartz_coercion f⟩

end WavefrontSet

namespace WavefrontSet

/--
[toSphere_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma toSphere_neg
  {n : ℕ}
  {n}
  {p : ClosedBall n}
-- given
  (hp : ‖p.val‖ = 1) :
-- imply
  (-p).toSphere (by rw [ClosedBall.norm_neg_eq]; exact hp) = ConeSupport.sphereNeg (p.toSphere hp) := by
-- proof
  apply Subtype.ext
  simp [ClosedBall.toSphere, ConeSupport.sphereNeg, ClosedBall.neg_val]

end WavefrontSet

namespace WavefrontSet

/--
[toEuclidean_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma toEuclidean_neg
  {n : ℕ}
  {n}
  {p : ClosedBall n}
-- given
  (hp : ‖p.val‖ < 1) :
-- imply
  (-p).toEuclidean (by rw [ClosedBall.norm_neg_eq]; exact hp) = -(p.toEuclidean hp) := by
-- proof
  simp [ClosedBall.toEuclidean, ClosedBall.neg_val, smul_neg]

end WavefrontSet

namespace WavefrontSet

/--
[mem_css_iff_neg_mem_css_fourier_fourier](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma mem_css_iff_neg_mem_css_fourier_fourier
  {n : ℕ}
  {n}
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {p : ClosedBall n} :
-- imply
  p ∈ Css u ↔ (-p) ∈ Css (𝓕 (𝓕 u)) := by
-- proof
  rw [doubleFourier_eq_reflection]
  simp only [Css, mem_setOf_eq]
  have hneg : ‖(-p).val‖ = ‖p.val‖ := by rw [ClosedBall.neg_val, norm_neg]
  constructor
  ·
    intro hp_css
    by_cases h_pos : ‖p.val‖ = 1
    ·
      have h_neg : ‖(-p).val‖ = 1 := by rwa [hneg]
      simp only [dif_pos h_pos] at hp_css
      simp only [dif_pos h_neg]
      rw [toSphere_neg p h_pos, ConeSupport.css_reflection]
      rw [ConeSupport.mem_negSet_iff]
      rwa [ConeSupport.sphereNeg_sphereNeg]
    ·
      have h_neg : ‖(-p).val‖ ≠ 1 := by rwa [hneg]
      have hp_lt : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h_pos
      simp only [dif_neg h_pos] at hp_css
      simp only [dif_neg h_neg]
      rw [toEuclidean_neg]
      rw [singularSupport_reflection]
      rwa [neg_neg]
  ·
    intro hnp_css
    by_cases h_pos : ‖p.val‖ = 1
    ·
      have h_neg : ‖(-p).val‖ = 1 := by rwa [hneg]
      simp only [dif_pos h_neg] at hnp_css
      simp only [dif_pos h_pos]
      rw [toSphere_neg p h_pos, ConeSupport.css_reflection, ConeSupport.mem_negSet_iff] at hnp_css
      rwa [ConeSupport.sphereNeg_sphereNeg] at hnp_css
    ·
      have h_neg : ‖(-p).val‖ ≠ 1 := by rwa [hneg]
      have hp_lt : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h_pos
      simp only [dif_neg h_neg] at hnp_css
      simp only [dif_neg h_pos]
      rwa [toEuclidean_neg, singularSupport_reflection, neg_neg] at hnp_css

end WavefrontSet

namespace WavefrontSet

/--
[not_mem_css_iff_neg_not_mem_css_fourier_fourier](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma not_mem_css_iff_neg_not_mem_css_fourier_fourier
  {n : ℕ}
  {n}
  {u₁ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {p : ClosedBall n} :
-- imply
  p ∉ Css u₁ ↔ (-p) ∉ Css (𝓕 (𝓕 u₁)) :=
-- proof
  (mem_css_iff_neg_mem_css_fourier_fourier u₁ p).not

end WavefrontSet

namespace WavefrontSet

/--
[isSmoothNear_schwartzConvolution_local](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma isSmoothNear_schwartzConvolution_local
  {n : ℕ}
  {n}
  {u : TemperedDistribution (ConeSupport.E n) ℂ}
  {φ : SchwartzMap (ConeSupport.E n) ℂ}
  {x₀ : ConeSupport.E n} :
-- imply
  ConeSupport.IsSmoothNear (ConeSupport.schwartzConvolution u φ) x₀ :=
-- proof
  isSmoothNear_schwartzConvolution_local' u φ x₀

end WavefrontSet

namespace WavefrontSet

/--
[boundaryProd_swap_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma boundaryProd_swap_neg
  {n : ℕ}
  {n}
  {p q : ClosedBall n}
-- given
  (hpq : (p, q) ∈ BoundaryProd n) :
-- imply
  (q, -p) ∈ BoundaryProd n := by
-- proof
  simp only [BoundaryProd, Set.mem_setOf_eq, ClosedBall.norm_neg_eq] at hpq ⊢
  exact hpq.symm
/-- Transport of `WFsc` under the Fourier transform: if `(p, q) ∉ WFsc u`, then
`(q, -p) ∉ WFsc (𝓕 u)`. -/
end WavefrontSet
set_option maxHeartbeats 1600000
open scoped Topology
open Set
namespace WavefrontSet

end WavefrontSet

namespace WavefrontSet

/--
[scaleCLE_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma scaleCLE_apply
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  {a : ℝ}
  {x : E}
-- given
  (ha : a ≠ 0) :
-- imply
  scaleCLE a ha x = a • x := by
-- proof
  simp [scaleCLE]

end WavefrontSet

namespace WavefrontSet

/--
[sphere_subset_compl_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma sphere_subset_compl_zero
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F] :
-- imply
  Metric.sphere (0 : E) 1 ⊆ ({(0 : E)}ᶜ : Set E) := by
-- proof
  intro x hx h
  simp only [Metric.mem_sphere, dist_zero_right] at hx
  rw [h, norm_zero] at hx; exact zero_ne_one hx

end WavefrontSet

namespace WavefrontSet

/--
[norm_iteratedFDeriv_le_scale](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma norm_iteratedFDeriv_le_scale
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  {ψ : E → F}
  {a : ℝ}
  {x : E}
  {k : ℕ}
-- given
  (hψ_hom : IsPositivelyHomogeneous 0 ψ)
  (ha : 0 < a)
  (hx : x ≠ 0) :
-- imply
  ‖iteratedFDeriv ℝ k ψ x‖ ≤ ‖iteratedFDeriv ℝ k ψ (a • x)‖ * a ^ k := by
-- proof
  have ha' : a ≠ 0 := ne_of_gt ha
  have hax : a • x ≠ 0 := smul_ne_zero ha' hx
  have hopen : IsOpen ({(0 : E)}ᶜ : Set E) := isOpen_compl_singleton
  have : Nontrivial E := ⟨⟨x, 0, hx⟩⟩
  set s : Set E := {(0 : E)}ᶜ
  set g : E ≃L[ℝ] E := scaleCLE a ha'
  rw [← iteratedFDerivWithin_of_isOpen k hopen (show x ∈ s from hx),
    ← iteratedFDerivWithin_of_isOpen k hopen (show a • x ∈ s from hax)]
  have h_pre : (g : E → E) ⁻¹' s = s := by ext y; simp [g, s, ha']
  have h_eq : EqOn (ψ ∘ (g : E → E)) ψ s := fun y hy => by
    show ψ (g y) = ψ y; simp only [g, scaleCLE_apply]
    rw [hψ_hom a ha y hy]; simp
  have h_cle := g.iteratedFDerivWithin_comp_right ψ hopen.uniqueDiffOn
    (show g x ∈ s from show a • x ∈ s from hax) k
  rw [h_pre] at h_cle
  rw [← iteratedFDerivWithin_congr h_eq (show x ∈ s from hx) k, h_cle]
  set M := iteratedFDerivWithin ℝ k ψ s (g x)
  have h1 : ‖M.compContinuousLinearMap (fun _ => (g : E →L[ℝ] E))‖ ≤
    ‖M‖ * ∏ _ : Fin k, ‖(g : E →L[ℝ] E)‖ :=
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le M _
  have h3 : ‖(g : E →L[ℝ] E)‖ = a := by
    have : ((g : E ≃L[ℝ] E) : E →L[ℝ] E) = a • ContinuousLinearMap.id ℝ E := by ext; simp [g]
    rw [this, norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_of_nonneg ha.le]
  rw [Finset.prod_const, Finset.card_fin, h3,
    show ‖M‖ = ‖iteratedFDerivWithin ℝ k ψ s (a • x)‖ from by simp [g, M]] at h1
  exact h1

end WavefrontSet

namespace WavefrontSet

/--
[exists_bound_iteratedFDeriv_sphere](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma exists_bound_iteratedFDeriv_sphere
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [FiniteDimensional ℝ E]
  [Nontrivial E]
  {ψ : E → F}
  {k : ℕ}
-- given
  (hψ_smooth : ContDiffOn ℝ ⊤ ψ ({(0 : E)}ᶜ)) :
-- imply
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Metric.sphere (0 : E) 1, ‖iteratedFDeriv ℝ k ψ x‖ ≤ C := by
-- proof
  have hopen : IsOpen ({(0 : E)}ᶜ : Set E) := isOpen_compl_singleton
  have h_cont : ContinuousOn (fun x => iteratedFDeriv ℝ k ψ x) ({(0 : E)}ᶜ) :=
    (hψ_smooth.continuousOn_iteratedFDerivWithin (m := k) le_top hopen.uniqueDiffOn).congr
      (fun x hx => (iteratedFDerivWithin_of_isOpen k hopen hx).symm)
  have h_norm_cont : ContinuousOn (fun x => ‖iteratedFDeriv ℝ k ψ x‖)
    (Metric.sphere (0 : E) 1) :=
    continuous_norm.comp_continuousOn (h_cont.mono sphere_subset_compl_zero)
  have h_nonempty : (Metric.sphere (0 : E) 1).Nonempty := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    exact ⟨‖x‖⁻¹ • x, by
      simp [norm_smul, norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩
  obtain ⟨x₀, hx₀_mem, hx₀_max⟩ :=
    (isCompact_sphere (0 : E) 1).exists_isMaxOn h_nonempty h_norm_cont
  exact ⟨‖iteratedFDeriv ℝ k ψ x₀‖, norm_nonneg _, fun x hx => hx₀_max hx⟩

end WavefrontSet

namespace WavefrontSet

/--
[norm_iteratedFDeriv_le_of_homogeneous_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma norm_iteratedFDeriv_le_of_homogeneous_zero
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [FiniteDimensional ℝ E]
  {ψ : E → F}
  {k : ℕ}
-- given
  (hψ_smooth : ContDiffOn ℝ ⊤ ψ ({(0 : E)}ᶜ))
  (hψ_hom : IsPositivelyHomogeneous 0 ψ) :
-- imply
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, x ≠ 0 → ‖iteratedFDeriv ℝ k ψ x‖ ≤ C * ‖x‖⁻¹ ^ k := by
-- proof
  by_cases hE : Subsingleton E
  · exact ⟨0, le_refl 0, fun x hx => absurd (Subsingleton.eq_zero x) hx⟩
  have hNT : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
  obtain ⟨C, hC_nonneg, hC_bound⟩ := exists_bound_iteratedFDeriv_sphere hψ_smooth k
  refine ⟨C, hC_nonneg, fun x hx => ?_⟩
  have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hx_inv_pos : 0 < ‖x‖⁻¹ := inv_pos.mpr hx_norm_pos
  have h_scale := norm_iteratedFDeriv_le_scale hψ_hom hx_inv_pos hx k
  have h_on_sphere : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : E) 1 := by
    simp [norm_smul, inv_mul_cancel₀ (ne_of_gt hx_norm_pos)]
  calc ‖iteratedFDeriv ℝ k ψ x‖
    ≤ ‖iteratedFDeriv ℝ k ψ (‖x‖⁻¹ • x)‖ * ‖x‖⁻¹ ^ k := h_scale
    _ ≤ C * ‖x‖⁻¹ ^ k :=
      mul_le_mul_of_nonneg_right (hC_bound _ h_on_sphere)
        (pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) k)
section Lemma12_5
open scoped SchwartzMap

end WavefrontSet

namespace WavefrontSet

/--
[disjointCss_of_conicPartitionData](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
lemma disjointCss_of_conicPartitionData
  {n : ℕ}
  {n : ℕ}
  {u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {P : ConicPartitionData u v}
  {i j : P.ι} :
-- imply
  ConeSupport.DisjointCssCondition (P.uPart i) (P.vPart j) := by
-- proof
  rw [ConeSupport.disjointCssCondition_iff_disjoint]
  exact (P.angSupp_neg_disjoint i j).mono (P.css_uPart_sub i)
    (Set.image_mono (P.css_vPart_sub j))
/-- From a `ConvolutionWFscCondition` between `u` and `v`, one can construct an
explicit conic partition (a `ConicPartitionData u v`) whose pieces have angularly
disjoint conic singular supports. This is Lemma 12.something — the technical input
behind defining convolution under the WFsc compatibility hypothesis. -/

end WavefrontSet

/--
[exists_conicCutoff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
private lemma exists_conicCutoff_eq
  {n : ℕ}
  {ω : Sphere n} :
-- imply
  ∃ (g : E n → ℂ), IsConicCutoffNear g ω := by
-- proof
  apply ConeSupport.exists_conicCutoff ω

/--
[ClosedBall.neg_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
private lemma neg_val_eq
  {n : ℕ}
  {p : ClosedBall n} :
-- imply
  (-p).val = -p.val := by
-- proof
  apply WavefrontSet.ClosedBall.neg_val n p

/--
[ClosedBall.neg_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean)
-/
@[path]
private lemma neg_neg_eq
  {n : ℕ}
  {p : ClosedBall n} :
-- imply
  -(-p) = p := by
-- proof
  apply WavefrontSet.ClosedBall.neg_neg n p


-- created on 2026-10-23
