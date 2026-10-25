import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.DifferentialAnalysis.code.ConeSupportCorollary
open MeasureTheory Set ConeSupport


/--
[smulLeftCLM_schwEmbed_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConeSupportCorollary.lean)
-/
@[path]
private lemma smulLeftCLM_schwEmbed_eq_eq
  {n : ℕ}
  {φ : E n → ℂ}
  {f : 𝓢(E n, ℂ)} :
-- imply
  TemperedDistribution.smulLeftCLM ℂ φ (schwEmbed f) = schwEmbed (SchwartzMap.smulLeftCLM ℂ φ f) := by
-- proof
  apply ConeSupport.smulLeftCLM_schwEmbed_eq φ f

/--
[singularSupport_compactPart_empty_of_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConeSupportCorollary.lean)
-/
@[path]
private lemma singularSupport_compactPart_empty_of_decomp_eq
  {n : ℕ}
  {u : 𝓢'(E n, ℂ)}
  {f : 𝓢(E n, ℂ)}
  {g : 𝓢'(E n, ℂ)}
-- given
  (hsing : singularSupport u = ∅)
  (hdecomp : u = schwEmbed f + g) :
-- imply
  singularSupport g = ∅ := by
-- proof
  apply ConeSupport.singularSupport_compactPart_empty_of_decomp hsing f g hdecomp

/--
[emptyCss_implies_schwartz_compact_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConeSupportCorollary.lean)
-/
@[path]
private lemma emptyCss_implies_schwartz_compact_decomp_eq
  {n : ℕ}
  {u : 𝓢'(E n, ℂ)}
-- given
  (hcss : ConicSingularSupportSphere u = ∅)
  (hsing : singularSupport u = ∅) :
-- imply
  ∃ (f : 𝓢(E n, ℂ)) (g : 𝓢'(E n, ℂ)), u = schwEmbed f + g ∧ IsCompactlySupportedDistribution g ∧ singularSupport g = ∅ := by
-- proof
  apply ConeSupport.emptyCss_implies_schwartz_compact_decomp u hcss hsing

/--
[smulLeftCLM_comp_eq_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConeSupportCorollary.lean)
-/
@[path]
private lemma smulLeftCLM_comp_eq_mul_eq
  {n : ℕ}
  {a b : E n → ℂ}
  {u : 𝓢'(E n, ℂ)}
-- given
  (ha : Function.HasTemperateGrowth a)
  (hb : Function.HasTemperateGrowth b)
  (hab : Function.HasTemperateGrowth (a * b)) :
-- imply
  TemperedDistribution.smulLeftCLM ℂ a (TemperedDistribution.smulLeftCLM ℂ b u) = TemperedDistribution.smulLeftCLM ℂ (a * b) u := by
-- proof
  apply ConeSupport.smulLeftCLM_comp_eq_mul a b u ha hb hab

/--
[smulLeftCLM_eq_self_of_one_on_support](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConeSupportCorollary.lean)
-/
@[path]
private lemma smulLeftCLM_eq_self_of_one_on_support_eq
  {n : ℕ}
  {g : 𝓢'(E n, ℂ)}
  {K : Set (E n)}
  {φ : E n → ℂ}
-- given
  (_hK : IsCompact K)
  (hK_supp : ∀ f : 𝓢(E n, ℂ), (Function.support (⇑f) ∩ K = ∅) → g f = 0)
  (_hφ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
  (_hφ_compact : HasCompactSupport φ)
  (hφ_one : ∀ x ∈ K, φ x = 1)
  (hφ_tg : Function.HasTemperateGrowth φ) :
-- imply
  TemperedDistribution.smulLeftCLM ℂ φ g = g := by
-- proof
  apply ConeSupport.smulLeftCLM_eq_self_of_one_on_support g K _hK hK_supp φ _hφ_smooth _hφ_compact hφ_one hφ_tg

/--
[smulLeftCLM_schwartz_of_supported_in_smooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConeSupportCorollary.lean)
-/
@[path]
private lemma smulLeftCLM_schwartz_of_supported_in_smooth_eq
  {n : ℕ}
  {g : 𝓢'(E n, ℂ)}
  {φ : E n → ℂ}
  {ψ : E n → ℂ}
  {f : SchwartzMap (E n) ℂ}
-- given
  (hφ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
  (hφ_compact : HasCompactSupport φ)
  (hψ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
  (hψ_compact : HasCompactSupport ψ)
  (h_supp : tsupport φ ⊆ {y | ψ y ≠ 0})
  (hf : TemperedDistribution.smulLeftCLM ℂ ψ g = schwEmbed f) :
-- imply
  ∃ (s : SchwartzMap (E n) ℂ), TemperedDistribution.smulLeftCLM ℂ φ g = schwEmbed s := by
-- proof
  apply ConeSupport.smulLeftCLM_schwartz_of_supported_in_smooth g φ hφ_smooth hφ_compact ψ hψ_smooth hψ_compact h_supp f hf

/--
[smulLeftCLM_schwartz_of_emptySingSupp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConeSupportCorollary.lean)
-/
@[path]
private lemma smulLeftCLM_schwartz_of_emptySingSupp_eq
  {n : ℕ}
  {g : 𝓢'(E n, ℂ)}
  {φ : E n → ℂ}
-- given
  (hsing : singularSupport g = ∅)
  (hφ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
  (hφ_compact : HasCompactSupport φ)
  (_hφ_tg : Function.HasTemperateGrowth φ) :
-- imply
  ∃ (f : SchwartzMap (E n) ℂ), TemperedDistribution.smulLeftCLM ℂ φ g = schwEmbed f := by
-- proof
  apply ConeSupport.smulLeftCLM_schwartz_of_emptySingSupp g hsing φ hφ_smooth hφ_compact _hφ_tg

/--
[schwEmbed_compact_support_of_distrib_compact_support](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConeSupportCorollary.lean)
-/
@[path]
private lemma schwEmbed_compact_support_of_distrib_compact_support_eq
  {n : ℕ}
  {f : 𝓢(E n, ℂ)}
  {K : Set (E n)}
-- given
  (hK : IsCompact K)
  (hK_supp : ∀ ψ : 𝓢(E n, ℂ), (Function.support (⇑ψ) ∩ K = ∅) → (schwEmbed f) ψ = 0) :
-- imply
  Function.support (⇑f) ⊆ K := by
-- proof
  apply ConeSupport.schwEmbed_compact_support_of_distrib_compact_support f K hK hK_supp

/--
[compactlySupported_emptySingSupp_represented_by_smooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConeSupportCorollary.lean)
-/
@[path]
private lemma compactlySupported_emptySingSupp_represented_by_smooth_eq
  {n : ℕ}
  {g : 𝓢'(E n, ℂ)}
-- given
  (hcomp : IsCompactlySupportedDistribution g)
  (hsing : singularSupport g = ∅) :
-- imply
  ∃ (h : E n → ℂ), ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ ∀ ψ : 𝓢(E n, ℂ), g ψ = ∫ x, ψ x • h x := by
-- proof
  apply ConeSupport.compactlySupported_emptySingSupp_represented_by_smooth g hcomp hsing

/--
[compactSupport_emptySingSupp_isSchwartz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConeSupportCorollary.lean)
-/
@[path]
private lemma compactSupport_emptySingSupp_isSchwartz_eq
  {n : ℕ}
  {g : 𝓢'(E n, ℂ)}
-- given
  (hcomp : IsCompactlySupportedDistribution g)
  (hsing : singularSupport g = ∅) :
-- imply
  ∃ f : 𝓢(E n, ℂ), schwEmbed f = g := by
-- proof
  apply ConeSupport.compactSupport_emptySingSupp_isSchwartz g hcomp hsing

/--
[schwartz_conicSingularSupportSphere_empty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConeSupportCorollary.lean)
-/
@[path]
private lemma schwartz_conicSingularSupportSphere_empty_eq
  {n : ℕ}
  {f : 𝓢(E n, ℂ)} :
-- imply
  ConicSingularSupportSphere (schwEmbed f) = ∅ := by
-- proof
  apply ConeSupport.schwartz_conicSingularSupportSphere_empty f

/--
[coneSingularSupport_eq_empty_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConeSupportCorollary.lean)
-/
@[path]
private lemma coneSingularSupport_eq_empty_iff_eq
  {n : ℕ}
  {u : 𝓢'(E n, ℂ)} :
-- imply
  coneSingularSupport u = ∅ ↔ ∃ f : 𝓢(E n, ℂ), schwEmbed f = u := by
-- proof
  apply ConeSupport.coneSingularSupport_eq_empty_iff u


-- created on 2026-10-23
