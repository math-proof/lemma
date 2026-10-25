import Mathlib
import sympy.Basic
import Def.v1.Atlas.LieGroups.code.MeasuresSupport.Part2
open Filter Topology ConcreteMeasSupp


namespace ConcreteMeasSupp

/--
[cauchySeq_supportedIn_compact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MeasuresSupport.lean)
-/
@[path]
lemma cauchySeq_supportedIn_compact
  [TopologicalSpace X]
  [TopologicalSpace X]
  [LocallyCompactSpace X]
  [SecondCountableTopology X]
  [T2Space X]
  {μ : ℕ → (C(X, ℂ) →L[ℂ] ℂ)}
-- given
  (hcauchy : IsWeakStarCauchy μ) :
-- imply
  ∃ K : Set X, IsCompact K ∧ ∀ n, IsSupportedIn (μ n) K := by
-- proof
  obtain hempty | hne := isEmpty_or_nonempty X
  · exact ⟨∅, isCompact_empty, fun n f hf => by
    have : f = 0 := by ext x; exact IsEmpty.elim hempty x
    simp [this, map_zero]⟩
  haveI : BaireSpace C(X, ℂ) := inferInstance
  let A : ℕ → Set C(X, ℂ) := fun k => {f | ∀ n, ‖μ n f‖ ≤ ↑k}
  have A_closed : ∀ k, IsClosed (A k) := by
    intro k
    show IsClosed {f : C(X, ℂ) | ∀ n, ‖μ n f‖ ≤ ↑k}
    suffices h : {f : C(X, ℂ) | ∀ n, ‖μ n f‖ ≤ ↑k} =
      ⋂ n, (fun f => ‖μ n f‖) ⁻¹' Set.Iic ↑k by
      rw [h]
      exact isClosed_iInter fun n => IsClosed.preimage ((μ n).continuous.norm) isClosed_Iic
    ext f; simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
  have A_cover : ∀ f : C(X, ℂ), ∃ k, f ∈ A k := by
    intro f
    obtain ⟨R, _, hR⟩ := cauchySeq_bdd (hcauchy f)
    refine ⟨⌈‖μ 0 f‖ + R⌉₊, fun n => ?_⟩
    calc ‖μ n f‖ = ‖μ 0 f + (μ n f - μ 0 f)‖ := by ring_nf
      _ ≤ ‖μ 0 f‖ + ‖μ n f - μ 0 f‖ := norm_add_le _ _
      _ ≤ ‖μ 0 f‖ + dist (μ n f) (μ 0 f) := by rw [dist_eq_norm]
      _ ≤ ‖μ 0 f‖ + R := by linarith [hR n 0]
      _ ≤ ↑⌈‖μ 0 f‖ + R⌉₊ := Nat.le_ceil _
  have A_union : ⋃ k, A k = Set.univ := by
    ext f; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]; exact A_cover f
  obtain ⟨k, hk_int⟩ : ∃ k, (interior (A k)).Nonempty :=
    nonempty_interior_of_iUnion_of_closed A_closed A_union
  obtain ⟨g, hg⟩ := hk_int
  have hg_nhds : A k ∈ nhds g :=
    mem_nhds_iff.mpr ⟨interior (A k), interior_subset, isOpen_interior, hg⟩
  rw [UniformSpace.mem_nhds_iff] at hg_nhds
  obtain ⟨E, hE_mem, hE_sub⟩ := hg_nhds
  rw [ContinuousMap.mem_compactConvergence_entourage_iff] at hE_mem
  obtain ⟨K, V, hK, hV, hKV⟩ := hE_mem
  refine ⟨K, hK, fun n f hfK => ?_⟩
  by_contra hne
  have hmem : ∀ c : ℂ, ∀ m, ‖μ m (g + c • f)‖ ≤ ↑k := by
    intro c
    suffices g + c • f ∈ A k from this
    apply hE_sub
    apply hKV
    intro x hx
    simp only [ContinuousMap.coe_add, ContinuousMap.coe_smul, Pi.add_apply, Pi.smul_apply]
    rw [hfK x hx, smul_zero, add_zero]
    exact refl_mem_uniformity hV
  have hbound : ∀ (c : ℂ), ‖(μ n) g + c * (μ n) f‖ ≤ ↑k := by
    intro c
    have h := hmem c n
    rwa [map_add, map_smul, smul_eq_mul] at h
  set a := (μ n) g
  set b := (μ n) f
  have hb_ne : b ≠ 0 := hne
  have hscale : ∀ (t : ℕ), ‖a + ↑t‖ ≤ ↑k := by
    intro t
    have h := hbound (↑t / b)
    rwa [div_mul_cancel₀ _ hb_ne] at h
  set t := k + ⌈‖a‖⌉₊ + 1
  have h1 := hscale t
  have h2 : (↑t : ℝ) - ‖a‖ ≤ ‖a + (↑t : ℂ)‖ := by
    have h : ‖(↑t : ℂ)‖ ≤ ‖a‖ + ‖a + (↑t : ℂ)‖ := by
      calc ‖(↑t : ℂ)‖ = ‖-a + (a + ↑t)‖ := by ring_nf
        _ ≤ ‖-a‖ + ‖a + ↑t‖ := norm_add_le _ _
        _ = ‖a‖ + ‖a + ↑t‖ := by rw [norm_neg]
    rw [Complex.norm_natCast] at h
    linarith
  have h3 : (k : ℝ) < ↑t - ‖a‖ := by
    have h_ceil : ‖a‖ ≤ ↑⌈‖a‖⌉₊ := Nat.le_ceil ‖a‖
    show (k : ℝ) < ↑(k + ⌈‖a‖⌉₊ + 1) - ‖a‖
    push_cast
    linarith
  linarith
end ConcreteMeasSupp
namespace Meas
end Meas
namespace ConcreteMeasSupp

end ConcreteMeasSupp

namespace ConcreteMeasSupp

/--
[pointwiseLimitOfCLM_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MeasuresSupport.lean)
-/
@[path]
lemma pointwiseLimitOfCLM_continuous
  [TopologicalSpace X]
  [TopologicalSpace X]
  [LocallyCompactSpace X]
  [SecondCountableTopology X]
  [T2Space X]
  {μ : ℕ → (C(X, ℂ) →L[ℂ] ℂ)}
  {g : C(X, ℂ) →ₗ[ℂ] ℂ}
-- given
  (hlim : ∀ f : C(X, ℂ), Tendsto (fun n => μ n f) atTop (nhds (g f))) :
-- imply
  Continuous g := by
-- proof
  have htendsto : Tendsto (fun n (f : C(X, ℂ)) => μ n f) atTop (nhds (fun f => g f)) := by
    rwa [tendsto_pi_nhds]
  exact (continuousLinearMapOfTendsto μ htendsto).cont

end ConcreteMeasSupp

namespace ConcreteMeasSupp

/--
[weakStarCauchyLimit_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MeasuresSupport.lean)
-/
@[path]
lemma weakStarCauchyLimit_exists
  [TopologicalSpace X]
  [TopologicalSpace X]
  [LocallyCompactSpace X]
  [SecondCountableTopology X]
  [T2Space X]
  {μ : ℕ → (C(X, ℂ) →L[ℂ] ℂ)}
-- given
  (_hcauchy : IsWeakStarCauchy μ)
  (_hlim : ∀ f : C(X, ℂ), ∃ c : ℂ, Tendsto (fun n => μ n f) atTop (nhds c)) :
-- imply
  ∃ (μ₀ : C(X, ℂ) →L[ℂ] ℂ), TendstoWeakStar μ μ₀ := by
-- proof
  let limfun : C(X, ℂ) → ℂ := fun f => (_hlim f).choose
  have hlim_spec : ∀ f, Tendsto (fun n => μ n f) atTop (nhds (limfun f)) :=
    fun f => (_hlim f).choose_spec
  have htendsto_pi : Tendsto (fun n => (fun f => μ n f)) atTop (𝓝 limfun) := by
    rwa [tendsto_pi_nhds]
  let g : C(X, ℂ) →ₗ[ℂ] ℂ :=
    linearMapOfTendsto limfun (fun n => (μ n).toLinearMap) htendsto_pi
  have hg_eq : ∀ f, g f = limfun f := fun f => by
    simp [g, linearMapOfTendsto]
  have hg_lim : ∀ f, Tendsto (fun n => μ n f) atTop (nhds (g f)) := by
    intro f; rw [hg_eq]; exact hlim_spec f
  have hcont : Continuous g := pointwiseLimitOfCLM_continuous μ g hg_lim
  let μ₀ : C(X, ℂ) →L[ℂ] ℂ := ⟨g, hcont⟩
  exact ⟨μ₀, fun f => by exact hg_lim f⟩

end ConcreteMeasSupp

namespace ConcreteMeasSupp

/--
[seqComplete](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MeasuresSupport.lean)
-/
@[path]
lemma seqComplete
  [TopologicalSpace X]
  [LocallyCompactSpace X]
  [SecondCountableTopology X]
  [T2Space X]
  {μ : ℕ → (C(X, ℂ) →L[ℂ] ℂ)}
-- given
  (hcauchy : IsWeakStarCauchy μ) :
-- imply
  ∃ (K : Set X) (μ₀ : C(X, ℂ) →L[ℂ] ℂ), IsCompact K ∧ IsSupportedIn μ₀ K ∧ TendstoWeakStar μ μ₀ := by
-- proof
  obtain ⟨K, hK, hsupp⟩ := cauchySeq_supportedIn_compact μ hcauchy
  have hlim : ∀ f : C(X, ℂ), ∃ c : ℂ, Tendsto (fun n => μ n f) atTop (nhds c) := by
    intro f
    exact ⟨_, (hcauchy f).tendsto_limUnder⟩
  obtain ⟨μ₀, hμ₀_eq⟩ := weakStarCauchyLimit_exists μ hcauchy hlim
  refine ⟨K, μ₀, hK, ?_, ?_⟩
  · intro f hf
    have : ∀ n, μ n f = 0 := fun n => hsupp n f hf
    have htend : Tendsto (fun n => μ n f) atTop (nhds (μ₀ f)) := hμ₀_eq f
    have htend0 : Tendsto (fun n => μ n f) atTop (nhds 0) := by
      simp [this]
    exact tendsto_nhds_unique htend htend0
  · exact hμ₀_eq

end ConcreteMeasSupp

namespace ConcreteMeasSupp

/--
[isClosed_functionalSupport](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MeasuresSupport.lean)
-/
@[path]
lemma isClosed_functionalSupport
  [TopologicalSpace X]
  {μ : C(X, ℂ) →L[ℂ] ℂ} :
-- imply
  IsClosed (functionalSupport μ) := by
-- proof
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [Set.mem_compl_iff, functionalSupport, Set.mem_setOf_eq, not_forall] at hx
  obtain ⟨U, hU_nhds, hU_prop⟩ := hx
  push Not at hU_prop
  obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.mp hU_nhds
  apply mem_nhds_iff.mpr
  refine ⟨V, ?_, hVopen, hxV⟩
  intro y hyV
  simp only [Set.mem_compl_iff, functionalSupport, Set.mem_setOf_eq, not_forall]
  exact ⟨U, mem_nhds_iff.mpr ⟨V, hVU, hVopen, hyV⟩,
    by push Not; exact hU_prop⟩

end ConcreteMeasSupp

namespace ConcreteMeasSupp

/--
[not_in_support_local_vanishing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MeasuresSupport.lean)
-/
@[path]
lemma not_in_support_local_vanishing
  [TopologicalSpace X]
  [LocallyCompactSpace X]
  [SecondCountableTopology X]
  [T2Space X]
  {μ : C(X, ℂ) →L[ℂ] ℂ}
  {x : X}
-- given
  (hx : x ∉ functionalSupport μ) :
-- imply
  ∃ U ∈ nhds x, ∀ g : C(X, ℂ), (∀ y, y ∉ U → g y = 0) → μ g = 0 := by
-- proof
  simp only [functionalSupport, Set.mem_setOf_eq, not_forall] at hx
  obtain ⟨U, hU, hprop⟩ := hx
  push Not at hprop
  exact ⟨U, hU, hprop⟩

end ConcreteMeasSupp

namespace ConcreteMeasSupp

/--
[pou_kills_functional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MeasuresSupport.lean)
-/
@[path]
lemma pou_kills_functional
  [TopologicalSpace X]
  [TopologicalSpace X]
  [LocallyCompactSpace X]
  [SecondCountableTopology X]
  [T2Space X]
  {μ : C(X, ℂ) →L[ℂ] ℂ}
  {f : C(X, ℂ)}
  {g : ℕ → C(X, ℂ)}
-- given
  (hlf : LocallyFinite (fun n => Function.support (⇑(g n))))
  (hpw : ∀ x, HasSum (fun n => g n x) (f x))
  (hzero : ∀ n, μ (g n) = 0) :
-- imply
  μ f = 0 := by
-- proof
  have hsum : HasSum g f := by
    rw [HasSum]
    rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly]
    intro u hu x
    obtain ⟨t, ht_nhd, ht_fin⟩ := hlf x
    refine ⟨t, ht_nhd, ?_⟩
    simp only [SummationFilter.unconditional, Filter.eventually_atTop]
    use ht_fin.toFinset
    intro s hs y hy
    have hvan : ∀ n ∉ ht_fin.toFinset, (g n) y = 0 := by
      intro n hn
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hn
      have : y ∉ Function.support (⇑(g n)) := by
        intro hy_supp
        exact hn ⟨y, Set.mem_inter hy_supp hy⟩
      exact Function.notMem_support.mp this
    suffices h : (∑ n ∈ s, g n) y = f y by
      rw [h]; exact refl_mem_uniformity hu
    simp only [ContinuousMap.sum_apply]
    have h1 : ∑ n ∈ s, (g n) y = ∑ n ∈ ht_fin.toFinset, (g n) y :=
      (Finset.sum_subset hs (fun n _ hn' => hvan n hn')).symm
    rw [h1]
    exact (hasSum_sum_of_ne_finset_zero (fun n hn => hvan n hn)).unique (hpw y)
  have hμsum : HasSum (fun n => μ (g n)) (μ f) := μ.hasSum hsum
  have hμzero : HasSum (fun _ : ℕ => (0 : ℂ)) (μ f) := by
    convert hμsum using 1; ext n; exact (hzero n).symm
  exact hμzero.unique hasSum_zero
end ConcreteMeasSupp



-- created on 2026-10-23
