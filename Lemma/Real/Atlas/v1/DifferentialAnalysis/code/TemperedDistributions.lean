import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.TemperedDistributions
open SchwartzMap MeasureTheory ContinuousLinearMap TemperedDistributions
open scoped SchwartzMap ENNReal NNReal LineDeriv
open scoped ContDiff
open Distribution TemperedDistribution MeasureTheory.Measure Filter Topology


namespace TemperedDistributions

/--
[continuous_of_seminorm_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TemperedDistributions.lean)
-/
@[path]
lemma continuous_of_seminorm_bound
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {u : 𝓢(E, ℂ) →ₗ[ℂ] ℂ}
-- given
  (hbound : ∃ (s : Finset (ℕ × ℕ)) (C : NNReal), (normSeminorm ℂ ℂ).comp u ≤ C • s.sup (schwartzSeminormFamily ℂ E ℂ)) :
-- imply
  Continuous u :=
-- proof
  (schwartz_withSeminorms ℂ E ℂ).continuous_normedSpace_rng ℂ u hbound

end TemperedDistributions

namespace TemperedDistributions

/--
[seminorm_bound_of_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TemperedDistributions.lean)
-/
@[path]
lemma seminorm_bound_of_continuous
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {u : 𝓢(E, ℂ) →L[ℂ] ℂ} :
-- imply
  ∃ (s : Finset (ℕ × ℕ)) (C : NNReal), (normSeminorm ℂ ℂ).comp u.toLinearMap ≤ C • s.sup (schwartzSeminormFamily ℂ E ℂ) := by
-- proof
  have hcont : Continuous ((normSeminorm ℂ ℂ).comp u.toLinearMap) := by
    show Continuous (fun x => ‖u x‖)
    exact continuous_norm.comp u.continuous
  obtain ⟨s, C, _, hle⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ) _ hcont
  exact ⟨s, C, hle⟩

end TemperedDistributions

namespace TemperedDistributions

/--
[continuous_iff_seminorm_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TemperedDistributions.lean)
-/
@[path]
lemma continuous_iff_seminorm_bound
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {u : 𝓢(E, ℂ) →ₗ[ℂ] ℂ} :
-- imply
  Continuous u ↔ ∃ (s : Finset (ℕ × ℕ)) (C : NNReal), (normSeminorm ℂ ℂ).comp u ≤ C • s.sup (schwartzSeminormFamily ℂ E ℂ) := by
-- proof
  constructor
  · intro hcont
    exact seminorm_bound_of_continuous ⟨u, hcont⟩
  · exact continuous_of_seminorm_bound u

end TemperedDistributions

namespace TemperedDistributions

/--
[distribDerivCLM_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TemperedDistributions.lean)
-/
@[path]
lemma distribDerivCLM_apply
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {m : E}
  {u : 𝓢'(E, F)}
  {φ : 𝓢(E, ℂ)} :
-- imply
  distribDerivCLM m u φ = u (-(∂_{m} φ)) :=
-- proof
  TemperedDistribution.lineDerivOp_apply_apply u φ m

end TemperedDistributions

namespace TemperedDistributions

/--
[distribMulCLM_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TemperedDistributions.lean)
-/
@[path]
lemma distribMulCLM_apply
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {g : E → ℂ}
  {u : 𝓢'(E, F)}
  {φ : 𝓢(E, ℂ)} :
-- imply
  distribMulCLM g u φ = u (SchwartzMap.smulLeftCLM ℂ g φ) :=
-- proof
  TemperedDistribution.smulLeftCLM_apply_apply g u φ
section Lemma71
open scoped ContDiff

end TemperedDistributions

namespace TemperedDistributions

/--
[schwartz_iff_oneAddNorm_decay](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TemperedDistributions.lean)
-/
@[path]
lemma schwartz_iff_oneAddNorm_decay
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [NormedAddCommGroup G]
  [NormedSpace ℝ G]
  {f : E → G}
-- given
  (hsmooth : ContDiff ℝ ∞ f) :
-- imply
  (∀ k n : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) ↔ (∀ k n : ℕ, ∃ C : ℝ, ∀ x, (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) := by
-- proof
  constructor
  · intro hdecay k n
    let g : 𝓢(E, G) := ⟨f, hsmooth, hdecay⟩
    use 2 ^ k * (Finset.Iic ((k, n) : ℕ × ℕ)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g
    intro x
    have := SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℝ) (m := (k, n)) le_rfl le_rfl g x
    simpa using this
  · intro hdecay k n
    obtain ⟨C, hC⟩ := hdecay k n
    exact ⟨C, fun x => le_trans (by gcongr; linarith [norm_nonneg x]) (hC x)⟩

end TemperedDistributions

namespace TemperedDistributions

/--
[SchwartzMap.seminorm_derivCLM_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TemperedDistributions.lean)
-/
@[path]
lemma SchwartzMap.seminorm_derivCLM_le
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [NormedAddCommGroup G]
  [NormedSpace ℝ G]
  {𝕜 : Type*}
  [RCLike 𝕜]
  [NormedSpace 𝕜 G]
  [SMulCommClass ℝ 𝕜 G]
  {k n : ℕ}
  {f : 𝓢(ℝ, G)} :
-- imply
  SchwartzMap.seminorm 𝕜 k n (SchwartzMap.derivCLM 𝕜 G f) ≤ SchwartzMap.seminorm 𝕜 k (n + 1) f := by
-- proof
  apply SchwartzMap.seminorm_le_bound 𝕜 k n _ (by positivity)
  intro x
  have h : (SchwartzMap.derivCLM 𝕜 G f : ℝ → G) = deriv f := by ext; rfl
  rw [h, norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← iteratedDeriv_succ',
    ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact SchwartzMap.le_seminorm 𝕜 k (n + 1) f x

end TemperedDistributions

namespace TemperedDistributions

/--
[SchwartzMap.derivCLM_pow_eq_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TemperedDistributions.lean)
-/
@[path]
lemma SchwartzMap.derivCLM_pow_eq_iterate
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [NormedAddCommGroup G]
  [NormedSpace ℝ G]
  {𝕜 : Type*}
  [RCLike 𝕜]
  [NormedSpace 𝕜 G]
  [SMulCommClass ℝ 𝕜 G]
  {m : ℕ}
  {f : 𝓢(ℝ, G)} :
-- imply
  ((SchwartzMap.derivCLM 𝕜 G) ^ m) f = ((SchwartzMap.derivCLM 𝕜 G) : 𝓢(ℝ, G) → 𝓢(ℝ, G))^[m] f := by
-- proof
  induction m generalizing f with
  | zero => simp [Function.iterate_zero]
  | succ n ih =>
    rw [pow_succ, ContinuousLinearMap.mul_apply, Function.iterate_succ, Function.comp, ih]

end TemperedDistributions

namespace TemperedDistributions

/--
[monomial_hasTemperateGrowth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TemperedDistributions.lean)
-/
@[path]
lemma monomial_hasTemperateGrowth
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [NormedAddCommGroup G]
  [NormedSpace ℝ G]
  {𝕜 : Type*}
  [RCLike 𝕜]
  [NormedSpace 𝕜 G]
  [SMulCommClass ℝ 𝕜 G]
  {α : ℕ} :
-- imply
  (fun (x : ℝ) => x ^ α).HasTemperateGrowth := by
-- proof
fun_prop

end TemperedDistributions

namespace TemperedDistributions

/--
[seminorm_bound_of_continuous_linearMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TemperedDistributions.lean)
-/
@[path]
lemma seminorm_bound_of_continuous_linearMap
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [NormedAddCommGroup G]
  [NormedSpace ℝ G]
  {𝕜 : Type*}
  [RCLike 𝕜]
  [NormedSpace 𝕜 G]
  [SMulCommClass ℝ 𝕜 G]
  {T : 𝓢(E, G) →L[𝕜] 𝓢(E, G)} :
-- imply
  Seminorm.IsBounded (schwartzSeminormFamily 𝕜 E G) (schwartzSeminormFamily 𝕜 E G) T.toLinearMap := by
-- proof
  intro m
  have hcont : Continuous ((schwartzSeminormFamily 𝕜 E G m).comp T.toLinearMap) := by
    exact (schwartz_withSeminorms 𝕜 E G).continuous_seminorm m |>.comp T.continuous
  obtain ⟨s, C, _, hle⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms 𝕜 E G) _ hcont
  exact ⟨s, C, hle⟩

end TemperedDistributions

namespace TemperedDistributions

/--
[continuous_of_seminorm_bound_linearMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TemperedDistributions.lean)
-/
@[path]
lemma continuous_of_seminorm_bound_linearMap
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [NormedAddCommGroup G]
  [NormedSpace ℝ G]
  {𝕜 : Type*}
  [RCLike 𝕜]
  [NormedSpace 𝕜 G]
  [SMulCommClass ℝ 𝕜 G]
  {T : 𝓢(E, G) →ₗ[𝕜] 𝓢(E, G)}
-- given
  (hbound : Seminorm.IsBounded (schwartzSeminormFamily 𝕜 E G) (schwartzSeminormFamily 𝕜 E G) T) :
-- imply
  Continuous T :=
-- proof
  WithSeminorms.continuous_of_isBounded
    (schwartz_withSeminorms 𝕜 E G) (schwartz_withSeminorms 𝕜 E G) T hbound
section DsupportSchwartz
open scoped ContDiff
open Distribution TemperedDistribution MeasureTheory.Measure Filter Topology
variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [SecondCountableTopology E] [(volume : Measure E).IsAddHaarMeasure]
  [CompleteSpace F]

end TemperedDistributions

namespace TemperedDistributions

/--
[dsupport_schwartz_subset_tsupport](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TemperedDistributions.lean)
-/
@[path]
lemma dsupport_schwartz_subset_tsupport
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [FiniteDimensional ℝ E]
  [MeasureSpace E]
  [BorelSpace E]
  {ψ : 𝓢(E, F)} :
-- imply
  Distribution.dsupport (toTemperedDistributionCLM E F volume ψ) ⊆ tsupport (⇑ψ) := by
-- proof
  rw [← Set.compl_subset_compl]
  intro p hp
  rw [Set.mem_compl_iff] at hp
  rw [Set.mem_compl_iff, Distribution.notMem_dsupport_iff]
  refine ⟨(tsupport (⇑ψ))ᶜ, ?_, isOpen_compl_iff.mpr (isClosed_tsupport _), ?_⟩
  · intro φ hφ
    simp only [toTemperedDistributionCLM_apply_apply]
    exact integral_eq_zero_of_ae (Eventually.of_forall fun x => by
      by_cases hx : x ∈ tsupport (⇑φ)
      · simp [image_eq_zero_of_notMem_tsupport (hφ hx)]
      · simp [image_eq_zero_of_notMem_tsupport hx])
  · exact Set.mem_compl hp

end TemperedDistributions

namespace TemperedDistributions

/--
[support_subset_dsupport_schwartz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TemperedDistributions.lean)
-/
@[path]
lemma support_subset_dsupport_schwartz
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [FiniteDimensional ℝ E]
  [MeasureSpace E]
  [BorelSpace E]
  {ψ : 𝓢(E, F)} :
-- imply
  Function.support (⇑ψ) ⊆ Distribution.dsupport (toTemperedDistributionCLM E F volume ψ) := by
-- proof
  rw [← Set.compl_subset_compl]
  intro p hp
  rw [Set.mem_compl_iff, Distribution.notMem_dsupport_iff] at hp
  obtain ⟨U, hU_van, hU_open, hp_mem⟩ := hp
  rw [Set.mem_compl_iff, Function.mem_support, not_not]
  have h_test : ∀ (g : E → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
    tsupport g ⊆ U → ∫ x, g x • ψ x = 0 := by
    intro g hg_diff hg_cpt hg_tsup
    have hg_cpt' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hg_cpt.comp_left rfl
    have hg_diff' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) :=
      Complex.ofRealCLM.contDiff.comp hg_diff
    set φ := hg_cpt'.toSchwartzMap hg_diff'
    have hφ_tsup : tsupport (⇑φ) ⊆ U := by
      show tsupport (Complex.ofRealCLM ∘ g) ⊆ U
      exact (tsupport_comp_subset rfl _).trans hg_tsup
    have h_apply := hU_van φ hφ_tsup
    simp only [toTemperedDistributionCLM_apply_apply] at h_apply
    have h_integral_eq : (∫ x, g x • ψ x) = ∫ x, φ x • ψ x := by
      apply integral_congr_ae
      filter_upwards with x
      change g x • ψ x = (Complex.ofRealCLM ∘ g) x • ψ x
      rw [Function.comp_apply, Complex.ofRealCLM_apply, Complex.coe_smul]
    rwa [h_integral_eq]
  have hψ_loc_int : LocallyIntegrableOn (⇑ψ) U :=
    ψ.continuous.continuousOn.locallyIntegrableOn hU_open.measurableSet
  have h_ae_zero := hU_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero hψ_loc_int h_test
  have h_ae_restrict : (⇑ψ) =ᵐ[volume.restrict U] (0 : E → F) := by
    rw [EventuallyEq, ae_restrict_iff' hU_open.measurableSet]
    filter_upwards [h_ae_zero] with x hx hxU
    exact hx hxU
  have h_eqOn : Set.EqOn (⇑ψ) 0 U :=
    eqOn_open_of_ae_eq h_ae_restrict hU_open
      ψ.continuous.continuousOn continuous_const.continuousOn
  exact h_eqOn hp_mem

end TemperedDistributions

namespace TemperedDistributions

/--
[dsupport_schwartz_eq_tsupport](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TemperedDistributions.lean)
-/
@[path]
lemma dsupport_schwartz_eq_tsupport
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [FiniteDimensional ℝ E]
  [MeasureSpace E]
  [BorelSpace E]
  {ψ : 𝓢(E, F)} :
-- imply
  Distribution.dsupport (toTemperedDistributionCLM E F volume ψ) = tsupport (⇑ψ) := by
-- proof
  apply Set.Subset.antisymm
  · exact dsupport_schwartz_subset_tsupport ψ
  · exact Distribution.isClosed_dsupport.closure_subset_iff.mpr
    (support_subset_dsupport_schwartz ψ)

end TemperedDistributions

namespace TemperedDistributions

/--
[dsupport_closed_and_eq_tsupport](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TemperedDistributions.lean)
-/
@[path]
lemma dsupport_closed_and_eq_tsupport
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [FiniteDimensional ℝ E]
  [MeasureSpace E]
  [BorelSpace E]
  {u : 𝓢'(E, F)}
  {ψ : 𝓢(E, F)} :
-- imply
  IsClosed (Distribution.dsupport u) ∧ Distribution.dsupport (toTemperedDistributionCLM E F volume ψ) = tsupport (⇑ψ) :=
-- proof
  ⟨Distribution.isClosed_dsupport, dsupport_schwartz_eq_tsupport ψ⟩
end TemperedDistributions



-- created on 2026-10-23
