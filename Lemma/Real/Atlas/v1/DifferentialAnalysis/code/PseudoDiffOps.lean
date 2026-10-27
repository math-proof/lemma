import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.DifferentialAnalysis.code.PseudoDiffOps
open MeasureTheory Set Function TemperedDistribution DifferentialOperators
open scoped SchwartzMap Pointwise


namespace DifferentialOperators

/--
[singularSupport_compact_of_compactSupport](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffOps.lean)
-/
@[path]
lemma singularSupport_compact_of_compactSupport
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hu : HasCompactSupport u) :
-- imply
  IsCompact (singularSupport u) := by
-- proof
  obtain ⟨K, hK_compact, hK_supp⟩ := hu
  have hclosed : IsClosed (singularSupport u) := by
    rw [← isOpen_compl_iff]
    apply isOpen_iff_forall_mem_open.mpr
    intro x₀ hx₀
    have hsmooth : isSmoothNear u x₀ := not_not.mp hx₀
    obtain ⟨U, hU_open, hx₀_mem, f, hf_smooth, hf_eq⟩ := hsmooth
    refine ⟨U, fun x₁ hx₁ => ?_, hU_open, hx₀_mem⟩
    exact not_not.mpr ⟨U, hU_open, hx₁, f, hf_smooth, hf_eq⟩
  have hsubset : singularSupport u ⊆ K := by
    intro x₀ hx₀
    by_contra hx₀K
    apply hx₀
    have hK_closed : IsClosed K := hK_compact.isClosed
    refine ⟨Kᶜ, hK_closed.isOpen_compl, hx₀K, 0, contDiff_const, fun φ hφ => ?_⟩
    have hsup : Function.support (⇑φ) ∩ K = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro y hy
      exact absurd (hφ y (not_not.mpr hy.2)) (mem_support.mp hy.1)
    rw [hK_supp φ hsup]
    simp [integral_zero]
  exact hK_compact.of_isClosed_subset hclosed hsubset

end DifferentialOperators

namespace DifferentialOperators

/--
[smulLeft_add_complement](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffOps.lean)
-/
@[path]
lemma smulLeft_add_complement
  {n : ℕ}
  {χ : EuclideanSpace ℝ (Fin n) → ℂ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hχ : Function.HasTemperateGrowth χ := by fun_prop) :
-- imply
  smulLeftCLM ℂ χ u + smulLeftCLM ℂ (1 - χ) u = u := by
-- proof
  have h1χ : Function.HasTemperateGrowth (1 - χ) :=
    (Function.HasTemperateGrowth.const (1 : ℂ)).sub hχ
  ext φ
  simp only [UniformConvergenceCLM.add_apply, smulLeftCLM_apply_apply]
  rw [← map_add u]
  congr 1
  ext x
  simp only [SchwartzMap.add_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply hχ, SchwartzMap.smulLeftCLM_apply_apply h1χ]
  simp [Pi.sub_apply, smul_eq_mul, sub_mul, one_mul]

end DifferentialOperators

namespace DifferentialOperators

/--
[support_schwartz_smulLeft_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffOps.lean)
-/
@[path]
lemma support_schwartz_smulLeft_subset
  {n : ℕ}
  {χ : EuclideanSpace ℝ (Fin n) → ℂ}
  {φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  Function.support (⇑(SchwartzMap.smulLeftCLM ℂ χ φ)) ⊆ Function.support (⇑φ) := by
-- proof
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro h
  apply hx
  unfold SchwartzMap.smulLeftCLM
  split
  · simp [SchwartzMap.bilinLeftCLM_apply, h]
  · simp

end DifferentialOperators

namespace DifferentialOperators

/--
[smulLeft_hasCompactSupport](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffOps.lean)
-/
@[path]
lemma smulLeft_hasCompactSupport
  {n : ℕ}
  {χ : EuclideanSpace ℝ (Fin n) → ℂ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hu : HasCompactSupport u) :
-- imply
  HasCompactSupport (smulLeftCLM ℂ χ u) := by
-- proof
  obtain ⟨K, hK_compact, hK_supp⟩ := hu
  exact ⟨K, hK_compact, fun φ hφ => by
    simp only [smulLeftCLM_apply_apply]
    apply hK_supp
    rw [Set.eq_empty_iff_forall_notMem]
    intro y ⟨hy_supp, hy_K⟩
    have : y ∈ Function.support (⇑φ) := support_schwartz_smulLeft_subset χ φ hy_supp
    exact Set.eq_empty_iff_forall_notMem.mp hφ y ⟨this, hy_K⟩⟩

end DifferentialOperators

namespace DifferentialOperators

/--
[smulLeft_supported](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffOps.lean)
-/
@[path]
lemma smulLeft_supported
  {n : ℕ}
  {χ : EuclideanSpace ℝ (Fin n) → ℂ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {S : Set (EuclideanSpace ℝ (Fin n))}
-- given
  (hS : tsupport χ ⊆ S) :
-- imply
  ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (Function.support (⇑φ) ∩ S = ∅) → (smulLeftCLM ℂ χ u) φ = 0 := by
-- proof
  classical
  intro φ hφ
  rw [smulLeftCLM_apply_apply]
  suffices h : SchwartzMap.smulLeftCLM ℂ χ φ = 0 by
    rw [h, map_zero]
  by_cases hg : HasTemperateGrowth χ
  · ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply hg]
    simp only [SchwartzMap.coe_zero, Pi.zero_apply]
    by_cases hx : x ∈ support (⇑φ)
    · have hxS : x ∉ S := fun hxS =>
      (eq_empty_iff_forall_notMem.mp hφ) x ⟨hx, hxS⟩
      have hx_notin_supp : x ∉ support χ := fun h =>
        hxS (hS (subset_tsupport χ h))
      rw [notMem_support.mp hx_notin_supp, zero_smul]
    · rw [notMem_support.mp hx, smul_zero]
  · change (if hg : HasTemperateGrowth χ
    then SchwartzMap.bilinLeftCLM (ContinuousLinearMap.lsmul ℂ ℂ).flip hg
    else 0) φ = 0
    rw [dif_neg hg]
    simp [ContinuousLinearMap.zero_apply]

end DifferentialOperators

namespace DifferentialOperators

/--
[exists_smooth_bump_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffOps.lean)
-/
@[path]
lemma exists_smooth_bump_subset
  {n : ℕ}
  {F : Set (EuclideanSpace ℝ (Fin n))}
  {K : Set (EuclideanSpace ℝ (Fin n))}
-- given
  (hF : IsClosed F)
  (hK : IsCompact K)
  (hFK : F ⊆ interior K) :
-- imply
  ∃ χ : EuclideanSpace ℝ (Fin n) → ℂ, ContDiff ℝ (↑(⊤ : ℕ∞)) χ ∧ _root_.HasCompactSupport χ ∧ tsupport χ ⊆ K ∧ (∃ V : Set (EuclideanSpace ℝ (Fin n)), IsOpen V ∧ F ⊆ V ∧ ∀ x ∈ V, χ x = 1) := by
-- proof
  obtain ⟨f, hf_one, hf_zero, _⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior
      (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (n := ⊤) (s := F) (t := K) hF hFK
  let χ : EuclideanSpace ℝ (Fin n) → ℂ := fun x => ((f : EuclideanSpace ℝ (Fin n) → ℝ) x : ℂ)
  have hf_contDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) (f : EuclideanSpace ℝ (Fin n) → ℝ) :=
    contMDiff_iff_contDiff.mp f.2
  have hsmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) χ :=
    Complex.ofRealCLM.contDiff.comp hf_contDiff
  have hsupp : Function.support (f : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ K := by
    intro x hx
    rw [Function.mem_support] at hx
    by_contra h
    exact hx (hf_zero x h)
  have htsupp : tsupport χ ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    rw [Function.mem_support] at hx
    have hxne : (f : EuclideanSpace ℝ (Fin n) → ℝ) x ≠ 0 := by
      intro heq; apply hx; simp [χ, heq]
    exact hsupp (Function.mem_support.mpr hxne)
  have hcompsupp : _root_.HasCompactSupport χ :=
    hK.of_isClosed_subset (isClosed_tsupport χ) htsupp
  refine ⟨χ, hsmooth, hcompsupp, htsupp, ?_⟩
  rw [eventually_nhdsSet_iff_forall] at hf_one
  refine ⟨interior {x | (f : EuclideanSpace ℝ (Fin n) → ℝ) x = 1}, isOpen_interior, ?_, ?_⟩
  · intro x hx
    exact mem_interior_iff_mem_nhds.mpr (hf_one x hx)
  · intro x hx
    have hfx := interior_subset hx
    simp only [χ, Set.mem_setOf_eq] at hfx ⊢
    rw [hfx, Complex.ofReal_one]

end DifferentialOperators

namespace DifferentialOperators

/--
[distribConvolution_vanishesOn_compl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffOps.lean)
-/
@[path]
lemma distribConvolution_vanishesOn_compl
  {n : ℕ}
  {μ f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {K₁ K₂ : Set (EuclideanSpace ℝ (Fin n))}
-- given
  (hμ : HasCompactSupport μ)
  (hμK : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (Function.support (⇑φ) ∩ K₁ = ∅) → μ φ = 0)
  (hfK : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (Function.support (⇑φ) ∩ K₂ = ∅) → f φ = 0) :
-- imply
  vanishesOn (distribConvolution μ f hμ) (K₁ + K₂)ᶜ := by
-- proof
  intro φ hφ
  apply hfK
  rw [Set.eq_empty_iff_forall_notMem]
  intro x ⟨hx_supp, hx_K₂⟩
  have hconv_zero : (convolutionSchwartzCLM μ hμ φ).1 x = 0 := by
    show μ (SchwartzMap.compSubConstCLM ℂ (-x) φ) = 0
    apply hμK
    rw [Set.eq_empty_iff_forall_notMem]
    intro y ⟨hy_supp, hy_K₁⟩
    have hmem : y + x ∈ K₁ + K₂ := Set.add_mem_add hy_K₁ hx_K₂
    have hvanish : φ (y + x) = 0 := hφ _ (by rwa [Set.mem_compl_iff, not_not])
    rw [Function.mem_support] at hy_supp
    exact hy_supp (by simp only [SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]; exact hvanish)
  rw [Function.mem_support] at hx_supp
  exact hx_supp hconv_zero

end DifferentialOperators

namespace DifferentialOperators

/--
[isSmoothNear_of_vanishes_near](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffOps.lean)
-/
@[path]
lemma isSmoothNear_of_vanishes_near
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {p : EuclideanSpace ℝ (Fin n)}
  {U : Set (EuclideanSpace ℝ (Fin n))}
-- given
  (hU : IsOpen U)
  (hp : p ∈ U)
  (hv : vanishesOn u U) :
-- imply
  isSmoothNear u p := by
-- proof
  refine ⟨U, hU, hp, 0, contDiff_const, fun φ hφ => ?_⟩
  rw [hv φ hφ]
  simp [smul_zero, integral_zero]

end DifferentialOperators

namespace DifferentialOperators

/--
[isSmoothNear_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffOps.lean)
-/
@[path]
lemma isSmoothNear_add
  {n : ℕ}
  {u₁ u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {p : EuclideanSpace ℝ (Fin n)}
-- given
  (h₁ : isSmoothNear u₁ p)
  (h₂ : isSmoothNear u₂ p) :
-- imply
  isSmoothNear (u₁ + u₂) p := by
-- proof
  obtain ⟨U₁, hU₁_open, hp₁, f₁, hf₁_smooth, hf₁_eq⟩ := h₁
  obtain ⟨U₂, hU₂_open, hp₂, f₂, hf₂_smooth, hf₂_eq⟩ := h₂
  refine ⟨U₁ ∩ U₂, hU₁_open.inter hU₂_open, ⟨hp₁, hp₂⟩, f₁ + f₂,
    hf₁_smooth.add hf₂_smooth, ?_⟩
  intro φ hφ_supp
  have hφ₁ : ∀ y, y ∉ U₁ → φ y = 0 := fun y hy =>
    hφ_supp y (fun ⟨hyU₁, _⟩ => hy hyU₁)
  have hφ₂ : ∀ y, y ∉ U₂ → φ y = 0 := fun y hy =>
    hφ_supp y (fun ⟨_, hyU₂⟩ => hy hyU₂)
  simp only [UniformConvergenceCLM.add_apply]
  rw [hf₁_eq φ hφ₁, hf₂_eq φ hφ₂]
  have h_int₁ : Integrable (fun y => φ y • f₁ y) volume :=
    schwartz_smul_smooth_integrable u₁ U₁ hU₁_open f₁ hf₁_smooth hf₁_eq φ hφ₁
  have h_int₂ : Integrable (fun y => φ y • f₂ y) volume :=
    schwartz_smul_smooth_integrable u₂ U₂ hU₂_open f₂ hf₂_smooth hf₂_eq φ hφ₂
  simp_rw [Pi.add_apply, smul_add]
  exact (integral_add h_int₁ h_int₂).symm

end DifferentialOperators

namespace DifferentialOperators

/--
[distribConvolution_add_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffOps.lean)
-/
@[path]
lemma distribConvolution_add_left
  {n : ℕ}
  {μ₁ μ₂ f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hμ₁ : HasCompactSupport μ₁)
  (hμ₂ : HasCompactSupport μ₂)
  (hμ : HasCompactSupport (μ₁ + μ₂)) :
-- imply
  distribConvolution (μ₁ + μ₂) f hμ = distribConvolution μ₁ f hμ₁ + distribConvolution μ₂ f hμ₂ := by
-- proof
  ext φ
  show f (convolutionSchwartzCLM (μ₁ + μ₂) hμ φ) =
    f (convolutionSchwartzCLM μ₁ hμ₁ φ) + f (convolutionSchwartzCLM μ₂ hμ₂ φ)
  rw [← map_add f]
  congr 1

end DifferentialOperators

namespace DifferentialOperators

/--
[distribConvolution_add_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffOps.lean)
-/
@[path]
lemma distribConvolution_add_right
  {n : ℕ}
  {μ f₁ f₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hμ : HasCompactSupport μ) :
-- imply
  distribConvolution μ (f₁ + f₂) hμ = distribConvolution μ f₁ hμ + distribConvolution μ f₂ hμ :=
-- proof
  map_add (PointwiseConvergenceCLM.precomp ℂ (convolutionSchwartzCLM μ hμ)) f₁ f₂

end DifferentialOperators

namespace DifferentialOperators

/--
[exists_compact_neighborhood_disjoint_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffOps.lean)
-/
@[path]
lemma exists_compact_neighborhood_disjoint_sum
  {n : ℕ}
  {K₁ K₂ : Set (EuclideanSpace ℝ (Fin n))}
  {p : EuclideanSpace ℝ (Fin n)}
-- given
  (hK₁ : IsCompact K₁)
  (hK₂ : IsCompact K₂)
  (hp : p ∉ K₁ + K₂) :
-- imply
  ∃ (L₁ L₂ : Set (EuclideanSpace ℝ (Fin n))), IsCompact L₁ ∧ IsCompact L₂ ∧ K₁ ⊆ interior L₁ ∧ K₂ ⊆ interior L₂ ∧ p ∉ L₁ + L₂ := by
-- proof
  have hprod : K₁ ×ˢ K₂ ⊆ (fun xy : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => xy.1 + xy.2) ⁻¹' {p}ᶜ := by
    intro ⟨x, y⟩ ⟨hx, hy⟩ hmem
    apply hp
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hmem
    exact ⟨x, hx, y, hy, hmem⟩
  have hopen : IsOpen ((fun xy : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => xy.1 + xy.2) ⁻¹' {p}ᶜ) :=
    isOpen_compl_iff.mpr (isClosed_singleton.preimage (continuous_fst.add continuous_snd))
  obtain ⟨U₁, U₂, hU₁_open, hU₂_open, hK₁U₁, hK₂U₂, hprod_sub⟩ :=
    generalized_tube_lemma hK₁ hK₂ hopen hprod
  obtain ⟨L₁, hL₁_compact, hK₁_int, hL₁_sub⟩ := exists_compact_between hK₁ hU₁_open hK₁U₁
  obtain ⟨L₂, hL₂_compact, hK₂_int, hL₂_sub⟩ := exists_compact_between hK₂ hU₂_open hK₂U₂
  refine ⟨L₁, L₂, hL₁_compact, hL₂_compact, hK₁_int, hK₂_int, ?_⟩
  intro hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  have hab_mem : (a, b) ∈ U₁ ×ˢ U₂ := ⟨hL₁_sub ha, hL₂_sub hb⟩
  have := hprod_sub hab_mem
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at this
  exact this hab

end DifferentialOperators

namespace DifferentialOperators

/--
[singularSupport_smulLeft_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffOps.lean)
-/
@[path]
lemma singularSupport_smulLeft_subset
  {n : ℕ}
  {χ : EuclideanSpace ℝ (Fin n) → ℂ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) :
-- imply
  singularSupport (smulLeftCLM ℂ χ u) ⊆ singularSupport u := by
-- proof
  classical
  by_cases htemp : Function.HasTemperateGrowth χ
  · exact singularSupport_smulLeft_subset_of_temperate χ hχ htemp u
  ·
    have hSchwartzZero : SchwartzMap.smulLeftCLM ℂ χ = (0 : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) := by
      unfold SchwartzMap.smulLeftCLM
      split
      · exact absurd ‹_› htemp
      · rfl
    have hzero : smulLeftCLM ℂ χ u = 0 := by
      ext φ
      simp only [smulLeftCLM_apply_apply]
      rw [hSchwartzZero]
      simp
    intro x₀ hx₀
    exfalso
    apply hx₀
    rw [hzero]
    refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, 0, contDiff_const, fun φ _ => ?_⟩
    simp [integral_zero]

end DifferentialOperators

namespace DifferentialOperators

/--
[distribConvolution_four_term_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffOps.lean)
-/
@[path]
lemma distribConvolution_four_term_expansion
  {n : ℕ}
  {μ₁ μ₂ f₁ f₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hμ₁ : HasCompactSupport μ₁)
  (hμ₂ : HasCompactSupport μ₂)
  (hμ : HasCompactSupport (μ₁ + μ₂)) :
-- imply
  distribConvolution (μ₁ + μ₂) (f₁ + f₂) hμ = distribConvolution μ₁ f₁ hμ₁ + distribConvolution μ₁ f₂ hμ₁ + (distribConvolution μ₂ f₁ hμ₂ + distribConvolution μ₂ f₂ hμ₂) := by
-- proof
  rw [distribConvolution_add_left μ₁ μ₂ (f₁ + f₂) hμ₁ hμ₂ hμ,
    distribConvolution_add_right μ₁ f₁ f₂ hμ₁,
    distribConvolution_add_right μ₂ f₁ f₂ hμ₂]

end DifferentialOperators

namespace DifferentialOperators

/--
[distribConvolution_congr](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffOps.lean)
-/
@[path]
lemma distribConvolution_congr
  {n : ℕ}
  {a a' b b' : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (ha_eq : a = a')
  (hb_eq : b = b')
  (ha : HasCompactSupport a)
  (ha' : HasCompactSupport a') :
-- imply
  distribConvolution a b ha = distribConvolution a' b' ha' := by
-- proof
  subst ha_eq; subst hb_eq; rfl
/-- The singular support of a distributional convolution is contained in the Minkowski
sum of the singular supports of the factors: `singsupp (μ * f) ⊆ singsupp μ + singsupp f`.
This is the central property underlying pseudodifferential calculus (Melrose,
Section 12). -/

end DifferentialOperators

/--
[hasCompactDsupport_of_hasCompactSupport](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffOps.lean)
-/
@[path]
private lemma hasCompactDsupport_of_hasCompactSupport_eq
  {n : ℕ}
  {μ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hμ : HasCompactSupport μ) :
-- imply
  HasCompactDsupport μ := by
-- proof
  apply DifferentialOperators.hasCompactDsupport_of_hasCompactSupport μ hμ


-- created on 2026-10-23
