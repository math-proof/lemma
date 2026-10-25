import Mathlib
import sympy.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.WavefrontSetCorollaries
open MeasureTheory ConeSupport
open scoped SchwartzMap FourierTransform Pointwise


namespace ConeSupport

/--
[extConv_eq_of_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetCorollaries.lean)
-/
@[path]
lemma extConv_eq_of_decomp
  {n : ℕ}
  {u v : 𝓢'(E n, ℂ)}
  {d : SchwartzCompactDecomp u}
-- given
  (h : HasExtendedConvolution u v)
  (hu : ConicSingularSupportSphere u = ∅) :
-- imply
  extConv u v h = (standardConvolutionSystem v).convSchwartz d.schwartzPart + (standardConvolutionSystem v).convCompact d.compactPart := by
-- proof
  unfold extConv
  rw [dif_pos hu]
  exact convolution_decomp_well_defined_of_css_empty hu _ d

end ConeSupport

namespace ConeSupport

/--
[IsConicCutoffNear.mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetCorollaries.lean)
-/
@[path]
lemma IsConicCutoffNear.mul
  {n : ℕ}
  {ga gb : E n → ℂ}
  {ω : Sphere n}
-- given
  (ha : IsConicCutoffNear ga ω)
  (hb : IsConicCutoffNear gb ω) :
-- imply
  IsConicCutoffNear (ga * gb) ω := by
-- proof
  obtain ⟨hga_smooth, Ra, hRa, hRa_lt, R0a, hR0a, hsupp_a, ψa, hψa_hom, hψa_ne, hga_eq⟩ := ha
  obtain ⟨hgb_smooth, Rb, hRb, hRb_lt, R0b, hR0b, hsupp_b, ψb, hψb_hom, hψb_ne, hgb_eq⟩ := hb
  refine ⟨hga_smooth.mul hgb_smooth, max Ra Rb, lt_max_of_lt_left hRa,
    max_lt hRa_lt hRb_lt,
    max R0a R0b, lt_max_of_lt_left hR0a, ?_, ψa * ψb, ?_, ?_, ?_⟩
  ·
    intro x hx
    simp only [Set.mem_setOf_eq]
    have hx_ne : (ga * gb) x ≠ 0 := Function.mem_support.mp hx
    simp only [Pi.mul_apply] at hx_ne
    have hga_ne : ga x ≠ 0 := left_ne_zero_of_mul hx_ne
    have hgb_ne : gb x ≠ 0 := right_ne_zero_of_mul hx_ne
    have hRa_le := hsupp_a (Function.mem_support.mpr hga_ne)
    have hRb_le := hsupp_b (Function.mem_support.mpr hgb_ne)
    simp only [Set.mem_setOf_eq] at hRa_le hRb_le
    exact max_le hRa_le hRb_le
  ·
    intro c hc x hx
    simp [Pi.mul_apply, hψa_hom c hc x hx, hψb_hom c hc x hx]
  ·
    show ψa (ω : E n) * ψb (ω : E n) ≠ 0
    exact mul_ne_zero hψa_ne hψb_ne
  ·
    intro x hx
    simp only [Pi.mul_apply]
    have hRa' : Ra < ‖x‖ := lt_of_le_of_lt (le_max_left Ra Rb) hx
    have hRb' : Rb < ‖x‖ := lt_of_le_of_lt (le_max_right Ra Rb) hx
    rw [hga_eq x hRa', hgb_eq x hRb']

end ConeSupport

namespace ConeSupport

/--
[ConicSingularSupportSphere_add_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetCorollaries.lean)
-/
@[path]
lemma ConicSingularSupportSphere_add_subset
  {n : ℕ}
  {a b : 𝓢'(E n, ℂ)} :
-- imply
  ConicSingularSupportSphere (a + b) ⊆ ConicSingularSupportSphere a ∪ ConicSingularSupportSphere b := by
-- proof
  intro ω hω
  by_contra hω_not_union
  simp only [Set.mem_union, not_or] at hω_not_union
  obtain ⟨hω_not_a, hω_not_b⟩ := hω_not_union
  simp only [ConicSingularSupportSphere, Set.mem_setOf_eq, not_not] at hω_not_a hω_not_b
  obtain ⟨ga, hga_conic, fa, hfa⟩ := hω_not_a
  obtain ⟨gb, hgb_conic, fb, hfb⟩ := hω_not_b
  apply hω
  by_cases hga_temp : Function.HasTemperateGrowth ga
  · by_cases hgb_temp : Function.HasTemperateGrowth gb
    ·
      have hprod_conic := hga_conic.mul hgb_conic
      have hcomp_a : TemperedDistribution.smulLeftCLM ℂ (ga * gb) a =
        TemperedDistribution.smulLeftCLM ℂ gb (TemperedDistribution.smulLeftCLM ℂ ga a) :=
        (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hga_temp hgb_temp a).symm
      rw [hfa, smulLeftCLM_schwEmbed_eq gb fa] at hcomp_a
      have hcomm : (ga * gb : E n → ℂ) = gb * ga := mul_comm ga gb
      have hcomp_b : TemperedDistribution.smulLeftCLM ℂ (ga * gb) b =
        TemperedDistribution.smulLeftCLM ℂ ga (TemperedDistribution.smulLeftCLM ℂ gb b) := by
        rw [hcomm]
        exact (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hgb_temp hga_temp b).symm
      rw [hfb, smulLeftCLM_schwEmbed_eq ga fb] at hcomp_b
      have hlin := map_add (TemperedDistribution.smulLeftCLM ℂ (ga * gb)) a b
      rw [hcomp_a, hcomp_b, ← map_add schwEmbed] at hlin
      exact ⟨ga * gb, hprod_conic,
        SchwartzMap.smulLeftCLM ℂ gb fa + SchwartzMap.smulLeftCLM ℂ ga fb, hlin⟩
    ·
      have h0 : SchwartzMap.smulLeftCLM (𝕜 := ℂ) ℂ gb = 0 := by
        unfold SchwartzMap.smulLeftCLM; exact dif_neg hgb_temp
      exact ⟨gb, hgb_conic, 0, by
        ext φ
        simp [TemperedDistribution.smulLeftCLM_apply_apply, h0]⟩
  ·
    have h0 : SchwartzMap.smulLeftCLM (𝕜 := ℂ) ℂ ga = 0 := by
      unfold SchwartzMap.smulLeftCLM; exact dif_neg hga_temp
    exact ⟨ga, hga_conic, 0, by
      ext φ
      simp [TemperedDistribution.smulLeftCLM_apply_apply, h0]⟩

end ConeSupport

namespace ConeSupport

/--
[singularSupport_add_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetCorollaries.lean)
-/
@[path]
lemma singularSupport_add_subset
  {n : ℕ}
  {a b : 𝓢'(E n, ℂ)} :
-- imply
  singularSupport (a + b) ⊆ singularSupport a ∪ singularSupport b := by
-- proof
  intro x hx
  by_contra h_not_mem
  have ha_not : x ∉ singularSupport a :=
    fun h => h_not_mem (Set.mem_union_left _ h)
  have hb_not : x ∉ singularSupport b :=
    fun h => h_not_mem (Set.mem_union_right _ h)
  have ha : IsSmoothNear a x := by
    simp only [singularSupport, Set.mem_setOf_eq, not_not] at ha_not
    exact ha_not
  have hb : IsSmoothNear b x := by
    simp only [singularSupport, Set.mem_setOf_eq, not_not] at hb_not
    exact hb_not
  obtain ⟨φ_a, hφa_smooth, hφa_compact, hφa_ne, f_a, hf_a⟩ := ha
  obtain ⟨φ_b, hφb_smooth, hφb_compact, hφb_ne, f_b, hf_b⟩ := hb
  have hφa_temp : φ_a.HasTemperateGrowth := hφa_compact.hasTemperateGrowth hφa_smooth
  have hφb_temp : φ_b.HasTemperateGrowth := hφb_compact.hasTemperateGrowth hφb_smooth
  have hφ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ_a * φ_b) :=
    hφa_smooth.mul hφb_smooth
  have hφ_compact : HasCompactSupport (φ_a * φ_b) := hφa_compact.mul_right
  have hφ_ne : (φ_a * φ_b) x ≠ 0 := mul_ne_zero hφa_ne hφb_ne
  have ha_eq : TemperedDistribution.smulLeftCLM ℂ (φ_a * φ_b) a =
    TemperedDistribution.smulLeftCLM ℂ φ_b (TemperedDistribution.smulLeftCLM ℂ φ_a a) :=
    (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hφa_temp hφb_temp a).symm
  have ha_schwartz : TemperedDistribution.smulLeftCLM ℂ (φ_a * φ_b) a =
    schwEmbed (SchwartzMap.smulLeftCLM ℂ φ_b f_a) := by
    rw [ha_eq, hf_a, smulLeftCLM_schwEmbed_eq]
  have hb_eq : TemperedDistribution.smulLeftCLM ℂ (φ_b * φ_a) b =
    TemperedDistribution.smulLeftCLM ℂ φ_a (TemperedDistribution.smulLeftCLM ℂ φ_b b) :=
    (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hφb_temp hφa_temp b).symm
  have hb_schwartz : TemperedDistribution.smulLeftCLM ℂ (φ_a * φ_b) b =
    schwEmbed (SchwartzMap.smulLeftCLM ℂ φ_a f_b) := by
    rw [show φ_a * φ_b = φ_b * φ_a from mul_comm φ_a φ_b, hb_eq, hf_b, smulLeftCLM_schwEmbed_eq]
  have h_sum : TemperedDistribution.smulLeftCLM ℂ (φ_a * φ_b) (a + b) =
    schwEmbed (SchwartzMap.smulLeftCLM ℂ φ_b f_a + SchwartzMap.smulLeftCLM ℂ φ_a f_b) := by
    rw [map_add (TemperedDistribution.smulLeftCLM ℂ (φ_a * φ_b)) a b,
      ha_schwartz, hb_schwartz, map_add]
  have h_smooth : IsSmoothNear (a + b) x :=
    ⟨φ_a * φ_b, hφ_smooth, hφ_compact, hφ_ne,
      SchwartzMap.smulLeftCLM ℂ φ_b f_a + SchwartzMap.smulLeftCLM ℂ φ_a f_b, h_sum⟩
  exact absurd h_smooth (by rwa [singularSupport, Set.mem_setOf_eq] at hx)

end ConeSupport

namespace ConeSupport

/--
[singularSupport_extConv_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetCorollaries.lean)
-/
@[path]
lemma singularSupport_extConv_decomp
  {n : ℕ}
  {u v : 𝓢'(E n, ℂ)}
  {d : SchwartzCompactDecomp u}
-- given
  (h : HasExtendedConvolution u v)
  (hu : ConicSingularSupportSphere u = ∅) :
-- imply
  singularSupport (extConv u v h) ⊆ singularSupport ((standardConvolutionSystem v).convSchwartz d.schwartzPart) ∪ singularSupport ((standardConvolutionSystem v).convCompact d.compactPart) := by
-- proof
  rw [extConv_eq_of_decomp u v h hu d]
  exact singularSupport_add_subset _ _

end ConeSupport

namespace ConeSupport

/--
[smulLeft_schwartzConvolution_of_compactBump](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetCorollaries.lean)
-/
@[path]
lemma smulLeft_schwartzConvolution_of_compactBump
  {n : ℕ}
  {v : 𝓢'(E n, ℂ)}
  {φ : 𝓢(E n, ℂ)}
  {ψ : E n → ℂ}
-- given
  (hψ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
  (hψ_compact : HasCompactSupport ψ) :
-- imply
  ∃ f : 𝓢(E n, ℂ), TemperedDistribution.smulLeftCLM ℂ ψ (schwartzConvolution v φ) = schwEmbed f :=
-- proof
  smulLeftCLM_schwartzConvolution_eq_schwartz v φ ψ hψ_smooth hψ_compact

end ConeSupport

namespace ConeSupport

/--
[schwartzConvolution_isSmoothNear](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetCorollaries.lean)
-/
@[path]
lemma schwartzConvolution_isSmoothNear
  {n : ℕ}
  {v : 𝓢'(E n, ℂ)}
  {φ : 𝓢(E n, ℂ)}
  {x : E n} :
-- imply
  IsSmoothNear (schwartzConvolution v φ) x := by
-- proof
  have hx_nhds : (Set.univ : Set (E n)) ∈ nhds x := Filter.univ_mem
  obtain ⟨ψ₀, -, hψ₀_compact, hψ₀_smooth, -, hψ₀_x⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) hx_nhds
  let ψ : E n → ℂ := Complex.ofRealCLM ∘ ψ₀
  have hψ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ :=
    Complex.ofRealCLM.contDiff.comp hψ₀_smooth
  have hψ_compact : HasCompactSupport ψ := hψ₀_compact.comp_left (map_zero _)
  have hψ_x : ψ x ≠ 0 := by
    simp only [ψ, Function.comp, Complex.ofRealCLM_apply, Complex.ofReal_ne_zero, hψ₀_x]
    exact one_ne_zero
  obtain ⟨f, hf⟩ := smulLeft_schwartzConvolution_of_compactBump v φ ψ hψ_smooth hψ_compact
  exact ⟨ψ, hψ_smooth, hψ_compact, hψ_x, f, hf⟩

end ConeSupport

namespace ConeSupport

/--
[singularSupport_convSchwartz_empty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetCorollaries.lean)
-/
@[path]
lemma singularSupport_convSchwartz_empty
  {n : ℕ}
  {v : 𝓢'(E n, ℂ)}
  {φ : 𝓢(E n, ℂ)} :
-- imply
  singularSupport ((standardConvolutionSystem v).convSchwartz φ) = ∅ := by
-- proof
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  apply hx
  rw [standardConvolutionSystem_convSchwartz_eq]
  exact schwartzConvolution_isSmoothNear v φ x

end ConeSupport

namespace ConeSupport

/--
[isCompactlySupportedDistribution_iff_hasCompactSupport](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetCorollaries.lean)
-/
@[path]
lemma isCompactlySupportedDistribution_iff_hasCompactSupport
  {n : ℕ}
  {w : 𝓢'(E n, ℂ)} :
-- imply
  IsCompactlySupportedDistribution w ↔ DifferentialOperators.HasCompactSupport w :=
-- proof
  Iff.rfl

end ConeSupport

namespace ConeSupport

/--
[singularSupport_compactPart_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetCorollaries.lean)
-/
@[path]
lemma singularSupport_compactPart_subset
  {n : ℕ}
  {u : 𝓢'(E n, ℂ)}
  {d : SchwartzCompactDecomp u} :
-- imply
  singularSupport d.compactPart ⊆ singularSupport u := by
-- proof
  intro x hx
  rw [singularSupport, Set.mem_setOf_eq] at hx ⊢
  intro hu_smooth
  apply hx
  obtain ⟨φ, hφ_smooth, hφ_compact, hφ_ne, f_u, hf_u⟩ := hu_smooth
  refine ⟨φ, hφ_smooth, hφ_compact, hφ_ne, ?_⟩
  have hg_eq : d.compactPart = u - schwEmbed d.schwartzPart :=
    eq_sub_of_add_eq' d.sum_eq.symm
  refine ⟨f_u - SchwartzMap.smulLeftCLM ℂ φ d.schwartzPart, ?_⟩
  rw [hg_eq, map_sub, hf_u, smulLeftCLM_schwEmbed_eq, map_sub]

end ConeSupport

namespace ConeSupport

/--
[cssSphere_extConv_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetCorollaries.lean)
-/
@[path]
lemma cssSphere_extConv_decomp
  {n : ℕ}
  {u v : 𝓢'(E n, ℂ)}
  {d : SchwartzCompactDecomp u}
-- given
  (h : HasExtendedConvolution u v)
  (hu : ConicSingularSupportSphere u = ∅) :
-- imply
  ConicSingularSupportSphere (extConv u v h) ⊆ ConicSingularSupportSphere ((standardConvolutionSystem v).convSchwartz d.schwartzPart) ∪ ConicSingularSupportSphere ((standardConvolutionSystem v).convCompact d.compactPart) := by
-- proof
  rw [extConv_eq_of_decomp u v h hu d]
  exact ConicSingularSupportSphere_add_subset _ _

end ConeSupport

namespace ConeSupport

/--
[cssSphere_convSchwartz_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetCorollaries.lean)
-/
@[path]
lemma cssSphere_convSchwartz_subset
  {n : ℕ}
  {v : 𝓢'(E n, ℂ)}
  {φ : 𝓢(E n, ℂ)} :
-- imply
  ConicSingularSupportSphere ((standardConvolutionSystem v).convSchwartz φ) ⊆ ConicSingularSupportSphere v := by
-- proof
  rw [standardConvolutionSystem_convSchwartz_eq]
  exact css_schwartz_convolution v φ

end ConeSupport

namespace ConeSupport

/--
[standardConvolutionSystem_convCompact_add_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetCorollaries.lean)
-/
@[path]
lemma standardConvolutionSystem_convCompact_add_right
  {n : ℕ}
  {v₁ v₂ w : 𝓢'(E n, ℂ)} :
-- imply
  (standardConvolutionSystem (v₁ + v₂)).convCompact w = (standardConvolutionSystem v₁).convCompact w + (standardConvolutionSystem v₂).convCompact w := by
-- proof
  show compactDistribConv (v₁ + v₂) w = compactDistribConv v₁ w + compactDistribConv v₂ w
  exact compactDistribConv_add_right v₁ v₂ w

end ConeSupport

namespace ConeSupport

/--
[compactDistribConv_zero_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetCorollaries.lean)
-/
@[path]
lemma compactDistribConv_zero_right
  {n : ℕ}
  {w : 𝓢'(E n, ℂ)} :
-- imply
  compactDistribConv 0 w = 0 := by
-- proof
  have h := compactDistribConv_add_right (n := n) (0 : 𝓢'(E n, ℂ)) 0 w
  simp only [add_zero] at h
  have := add_left_cancel (a := compactDistribConv (0 : 𝓢'(E n, ℂ)) w)
    (show compactDistribConv 0 w + 0 = compactDistribConv 0 w + compactDistribConv 0 w
      from by rw [add_zero]; exact h)
  exact this.symm

end ConeSupport

namespace ConeSupport

/--
[smulLeftCLM_compactDistribConv_vanishing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetCorollaries.lean)
-/
@[path]
lemma smulLeftCLM_compactDistribConv_vanishing
  {n : ℕ}
  {v : 𝓢'(E n, ℂ)}
  {w : 𝓢'(E n, ℂ)}
  {g₀ : E n → ℂ}
-- given
  (hw : IsCompactlySupportedDistribution w)
  (hg₀_vanish : TemperedDistribution.smulLeftCLM ℂ g₀ v = 0) :
-- imply
  TemperedDistribution.smulLeftCLM ℂ g₀ (compactDistribConv v w) = 0 := by
-- proof
  rw [smulLeftCLM_compactDistribConv_comm v w hw g₀, hg₀_vanish,
    compactDistribConv_zero_right]

end ConeSupport

namespace ConeSupport

/--
[conicCutoff_smul_compactConvolution_schwartz_of_vanishing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetCorollaries.lean)
-/
@[path]
lemma conicCutoff_smul_compactConvolution_schwartz_of_vanishing
  {n : ℕ}
  {v : 𝓢'(E n, ℂ)}
  {w : 𝓢'(E n, ℂ)}
  {g₀ : E n → ℂ}
  {ω : Sphere n}
-- given
  (hw : IsCompactlySupportedDistribution w)
  (hg₀ : IsConicCutoffNear g₀ ω)
  (hg₀_vanish : TemperedDistribution.smulLeftCLM ℂ g₀ v = 0) :
-- imply
  ∃ (f : SchwartzMap (E n) ℂ), TemperedDistribution.smulLeftCLM ℂ g₀ ((standardConvolutionSystem v).convCompact w) = (f : 𝓢'(E n, ℂ)) := by
-- proof
  refine ⟨0, ?_⟩
  have h := smulLeftCLM_compactDistribConv_vanishing v w hw g₀ hg₀_vanish
  simp only [standardConvolutionSystem] at *
  rw [h, map_zero]

end ConeSupport

namespace ConeSupport

/--
[cssSphere_convCompact_coneSupportDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetCorollaries.lean)
-/
@[path]
lemma cssSphere_convCompact_coneSupportDisjoint
  {n : ℕ}
  {v w : 𝓢'(E n, ℂ)}
  {Γ : Set (Sphere n)}
-- given
  (hw : IsCompactlySupportedDistribution w)
  (hdisjoint : Disjoint (ConicSupportSphere v) Γ) :
-- imply
  Disjoint (ConicSingularSupportSphere ((standardConvolutionSystem v).convCompact w)) Γ := by
-- proof
  rw [Set.disjoint_left]
  intro ω hω_css hω_Γ
  have hω_not_csp : ω ∉ ConicSupportSphere v :=
    Set.disjoint_right.mp hdisjoint hω_Γ
  simp only [ConicSupportSphere, Set.mem_setOf_eq, not_not] at hω_not_csp
  obtain ⟨g₀, hg₀_conic, hg₀_zero⟩ := hω_not_csp
  obtain ⟨f, hf⟩ := conicCutoff_smul_compactConvolution_schwartz_of_vanishing
    v w hw g₀ ω hg₀_conic hg₀_zero
  exact hω_css ⟨g₀, hg₀_conic, f, hf⟩

end ConeSupport

namespace ConeSupport

/--
[cssSphere_add_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetCorollaries.lean)
-/
@[path]
lemma cssSphere_add_subset
  {n : ℕ}
  {u₁ u₂ : 𝓢'(E n, ℂ)} :
-- imply
  ConicSingularSupportSphere (u₁ + u₂) ⊆ ConicSingularSupportSphere u₁ ∪ ConicSingularSupportSphere u₂ :=
-- proof
  ConicSingularSupportSphere_add_subset u₁ u₂
/-- Convolution with a compactly supported distribution does not enlarge the conic singular
support on the sphere: `CSS_sphere (v * w) ⊆ CSS_sphere v`. -/
end ConeSupport



-- created on 2026-10-23
