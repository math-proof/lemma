import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators
open TemperedDistribution MvPolynomial SchwartzMap MeasureTheory Distribution DifferentialOperators DifferentialOperators.SmoothZeroAtInfty
open scoped SchwartzMap
open Filter Topology
open scoped Pointwise
open MeasureTheory
open SchwartzMap MeasureTheory Distribution
open scoped Topology
open scoped SchwartzMap Topology
open Distribution SchwartzMap
open Function MvPolynomial


namespace DifferentialOperators

/--
[principalSymbol_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma principalSymbol_def
  {n : ℕ}
  {m : ℕ}
  {P : MvPolynomial (Fin n) ℂ} :
-- imply
  principalSymbol n m P = homogeneousComponent m P :=
-- proof
  rfl

end DifferentialOperators

namespace DifferentialOperators

/--
[smulLeftCLM_add_complement](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma smulLeftCLM_add_complement
  {n : ℕ}
  {n : ℕ}
  {χ : EuclideanSpace ℝ (Fin n) → ℂ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hχ : Function.HasTemperateGrowth χ) :
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
[smulLeft_globally_smooth_of_supported_in_smooth_region](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma smulLeft_globally_smooth_of_supported_in_smooth_region
  {n : ℕ}
  {n : ℕ}
  {χ : EuclideanSpace ℝ (Fin n) → ℂ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {U : Set (EuclideanSpace ℝ (Fin n))}
  {f : EuclideanSpace ℝ (Fin n) → ℂ}
-- given
  (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
  (hχ_supp : ∀ x, x ∉ U → χ x = 0)
  (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
  (hf_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (∀ y, y ∉ U → φ y = 0) → u φ = ∫ y, φ y • f y)
  (hχ_temp : Function.HasTemperateGrowth χ) :
-- imply
  ∀ y : EuclideanSpace ℝ (Fin n), isSmoothNear (smulLeftCLM ℂ χ u) y := by
-- proof
  intro y
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ y, χ * f, hχ_smooth.mul hf_smooth,
    fun φ _ => ?_⟩
  simp only [smulLeftCLM_apply_apply]
  have hχφ_supp : ∀ z, z ∉ U → (SchwartzMap.smulLeftCLM ℂ χ φ) z = 0 := by
    intro z hz
    simp only [SchwartzMap.smulLeftCLM]
    split
    · simp only [SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.lsmul_apply,
      ContinuousLinearMap.flip_apply]
      rw [hχ_supp z hz, zero_smul]
    · simp
  rw [hf_eq (SchwartzMap.smulLeftCLM ℂ χ φ) hχφ_supp]
  congr 1; ext z
  simp only [SchwartzMap.smulLeftCLM]
  split
  · simp only [SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.lsmul_apply,
    ContinuousLinearMap.flip_apply, Pi.mul_apply]
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  · exact absurd hχ_temp ‹_›

end DifferentialOperators

namespace DifferentialOperators

/--
[smulLeft_complement_vanishesOn](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma smulLeft_complement_vanishesOn
  {n : ℕ}
  {n : ℕ}
  {χ : EuclideanSpace ℝ (Fin n) → ℂ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {V : Set (EuclideanSpace ℝ (Fin n))}
-- given
  (hχ_one : ∀ x ∈ V, χ x = 1)
  (h1χ_temp : Function.HasTemperateGrowth (1 - χ)) :
-- imply
  vanishesOn (smulLeftCLM ℂ (1 - χ) u) V := by
-- proof
  intro φ hφ_supp
  simp only [smulLeftCLM_apply_apply]
  suffices h : SchwartzMap.smulLeftCLM ℂ (1 - χ) φ = 0 by rw [h, map_zero]
  ext x
  simp only [SchwartzMap.smulLeftCLM]
  split
  · simp only [SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.lsmul_apply,
    ContinuousLinearMap.flip_apply, SchwartzMap.zero_apply]
    by_cases hxV : x ∈ V
    · rw [show (1 - χ) x = 1 - χ x from rfl, hχ_one x hxV, sub_self, zero_smul]
    · rw [hφ_supp x hxV, smul_zero]
  · simp

end DifferentialOperators

namespace DifferentialOperators

/--
[smooth_plus_vanishing_is_smooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma smooth_plus_vanishing_is_smooth
  {n : ℕ}
  {n : ℕ}
  {v w : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {x₀ : EuclideanSpace ℝ (Fin n)}
  {U : Set (EuclideanSpace ℝ (Fin n))}
-- given
  (hU : IsOpen U)
  (hx : x₀ ∈ U)
  (hv : ∀ y : EuclideanSpace ℝ (Fin n), isSmoothNear v y)
  (hw : vanishesOn w U) :
-- imply
  isSmoothNear (v + w) x₀ := by
-- proof
  obtain ⟨V, hV_open, hx_V, f, hf_smooth, hv_eq⟩ := hv x₀
  refine ⟨V ∩ U, hV_open.inter hU, ⟨hx_V, hx⟩, f, hf_smooth, ?_⟩
  intro φ hφ_supp
  simp only [UniformConvergenceCLM.add_apply]
  have hφ_V : ∀ y, y ∉ V → φ y = 0 := fun y hy =>
    hφ_supp y (fun ⟨hyV, _⟩ => hy hyV)
  have hφ_U : ∀ y, y ∉ U → φ y = 0 := fun y hy =>
    hφ_supp y (fun ⟨_, hyU⟩ => hy hyU)
  rw [hv_eq φ hφ_V]
  rw [hw φ hφ_U, add_zero]

end DifferentialOperators

namespace DifferentialOperators

/--
[isSmoothNear_of_vanishesOn](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma isSmoothNear_of_vanishesOn
  {n : ℕ}
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {U : Set (EuclideanSpace ℝ (Fin n))}
  {x₀ : EuclideanSpace ℝ (Fin n)}
-- given
  (hU : IsOpen U)
  (hv : vanishesOn u U)
  (hx₀ : x₀ ∈ U) :
-- imply
  isSmoothNear u x₀ :=
-- proof
  ⟨U, hU, hx₀, 0, contDiff_const, fun φ hφ => by rw [hv φ hφ]; simp⟩
/-- If `u` is **globally smooth** (represented by a smooth `f`), then
`P(D) u` is also globally smooth — represented by an explicit smooth `g`
(the classical action of `P(D)` on `f`). -/
section SingularSupportInclusion
variable {n : ℕ}
/-- **Singular support is contracted by `P(D)`:**
`singsupp(P(D) u) ⊆ singsupp u`. -/
end SingularSupportInclusion
section WeakConvergence
open Filter Topology

end DifferentialOperators

namespace DifferentialOperators

/--
[tendsto_const_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma tendsto_const_smul
  {n : ℕ}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {p : Filter ι}
  {u : ι → 𝓢'(E, F)}
  {u₀ : 𝓢'(E, F)}
  {c : ℂ}
-- given
  (hu : Tendsto u p (𝓝 u₀)) :
-- imply
  Tendsto (fun j => c • u j) p (𝓝 (c • u₀)) :=
-- proof
  ((continuous_const_smul c).tendsto _).comp hu

end DifferentialOperators

namespace DifferentialOperators

/--
[tendsto_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma tendsto_add
  {n : ℕ}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {p : Filter ι}
  {u u' : ι → 𝓢'(E, F)}
  {u₀ u₀' : 𝓢'(E, F)}
-- given
  (hu : Tendsto u p (𝓝 u₀))
  (hu' : Tendsto u' p (𝓝 u₀')) :
-- imply
  Tendsto (fun j => u j + u' j) p (𝓝 (u₀ + u₀')) :=
-- proof
  hu.add hu'

end DifferentialOperators

namespace DifferentialOperators

/--
[tendsto_constCoeffDiffOp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma tendsto_constCoeffDiffOp
  {n : ℕ}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {n : ℕ}
  {p : Filter ι}
  {u : ι → 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {u₀ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {P : MvPolynomial (Fin n) ℂ}
-- given
  (hu : Tendsto u p (𝓝 u₀)) :
-- imply
  Tendsto (fun j => constCoeffDiffOp n P (u j)) p (𝓝 (constCoeffDiffOp n P u₀)) :=
-- proof
  ((constCoeffDiffOp n P).continuous.tendsto _).comp hu

end DifferentialOperators

namespace DifferentialOperators

/--
[tendsto_smul_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma tendsto_smul_left
  {n : ℕ}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {p : Filter ι}
  {u : ι → 𝓢'(E, F)}
  {u₀ : 𝓢'(E, F)}
  {g : E → ℂ}
-- given
  (hu : Tendsto u p (𝓝 u₀)) :
-- imply
  Tendsto (fun j => TemperedDistribution.smulLeftCLM F g (u j)) p (𝓝 (TemperedDistribution.smulLeftCLM F g u₀)) :=
-- proof
  ((TemperedDistribution.smulLeftCLM F g).continuous.tendsto _).comp hu

end DifferentialOperators

namespace DifferentialOperators

/--
[tendsto_smul_add_diffOp_smulLeft](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma tendsto_smul_add_diffOp_smulLeft
  {n : ℕ}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {n : ℕ}
  {p : Filter ι}
  {u u' : ι → 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {u₀ u₀' : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {c : ℂ}
  {P : MvPolynomial (Fin n) ℂ}
  {g : EuclideanSpace ℝ (Fin n) → ℂ}
-- given
  (hu : Tendsto u p (𝓝 u₀))
  (hu' : Tendsto u' p (𝓝 u₀')) :
-- imply
  Tendsto (fun j => c • u j) p (𝓝 (c • u₀)) ∧ Tendsto (fun j => u j + u' j) p (𝓝 (u₀ + u₀')) ∧ Tendsto (fun j => constCoeffDiffOp n P (u j)) p (𝓝 (constCoeffDiffOp n P u₀)) ∧ Tendsto (fun j => TemperedDistribution.smulLeftCLM ℂ g (u j)) p (𝓝 (TemperedDistribution.smulLeftCLM ℂ g u₀)) :=
-- proof
  ⟨tendsto_const_smul hu c, tendsto_add hu hu',
    tendsto_constCoeffDiffOp hu P, tendsto_smul_left hu g⟩
alias proposition_11_2 := tendsto_smul_add_diffOp_smulLeft
section HypoellipticRegularity
open scoped Pointwise

end DifferentialOperators

namespace DifferentialOperators

/--
[smooth_cutoff_near_zero_for_parametrix](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma smooth_cutoff_near_zero_for_parametrix
  {n : ℕ}
  {n}
  {n : ℕ} :
-- imply
  ∃ (φ : EuclideanSpace ℝ (Fin n) → ℂ), ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ Function.HasTemperateGrowth φ ∧ (∃ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U ∧ (0 : EuclideanSpace ℝ (Fin n)) ∈ U ∧ ∀ x ∈ U, φ x = 1) := by
-- proof
  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨fun x => (b x : ℂ), ?_, ?_, ?_, ?_⟩
  ·
    exact Complex.ofRealCLM.contDiff.comp b.contDiff
  ·
    exact b.hasCompactSupport.comp_left Complex.ofReal_zero
  ·
    exact (b.hasCompactSupport.comp_left Complex.ofReal_zero).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp b.contDiff)
  ·
    refine ⟨Metric.ball 0 1, Metric.isOpen_ball, Metric.mem_ball_self one_pos, ?_⟩
    intro x hx
    show (b x : ℂ) = 1
    have : b x = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    simp [this]

end DifferentialOperators

namespace DifferentialOperators

/--
[smulLeft_compactSupp_gives_compact_support](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma smulLeft_compactSupp_gives_compact_support
  {n : ℕ}
  {n}
  {n : ℕ}
  {φ : EuclideanSpace ℝ (Fin n) → ℂ}
  {F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
  (hφ_supp : HasCompactSupport φ)
  (hφ_temp : Function.HasTemperateGrowth φ) :
-- imply
  ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧ ∀ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (∀ y, y ∈ K → ψ y = 0) → (TemperedDistribution.smulLeftCLM ℂ φ F) ψ = 0 := by
-- proof
  refine ⟨tsupport φ, hφ_supp, fun ψ hψ => ?_⟩
  simp only [smulLeftCLM_apply_apply]
  suffices h : SchwartzMap.smulLeftCLM ℂ φ ψ = 0 by rw [h, map_zero]
  ext y
  simp only [SchwartzMap.smulLeftCLM_apply_apply hφ_temp, SchwartzMap.zero_apply]
  by_cases hy : y ∈ tsupport φ
  · rw [hψ y hy, smul_zero]
  · rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]

end DifferentialOperators

namespace DifferentialOperators

/--
[singularSupport_smulLeft_subset_of_temperate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma singularSupport_smulLeft_subset_of_temperate
  {n : ℕ}
  {n}
  {n : ℕ}
  {φ : EuclideanSpace ℝ (Fin n) → ℂ}
  {F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
  (hφ_temp : Function.HasTemperateGrowth φ) :
-- imply
  singularSupport (TemperedDistribution.smulLeftCLM ℂ φ F) ⊆ singularSupport F := by
-- proof
  intro x₀ hx₀
  simp only [singularSupport, Set.mem_setOf_eq] at hx₀ ⊢
  intro hF_smooth
  apply hx₀
  obtain ⟨U, hU_open, hx₀_U, f, hf_smooth, hf_eq⟩ := hF_smooth
  refine ⟨U, hU_open, hx₀_U, fun y => φ y * f y, hφ_smooth.mul hf_smooth, fun ψ hψ => ?_⟩
  rw [smulLeftCLM_apply_apply]
  have hφψ_supp : ∀ y, y ∉ U → (SchwartzMap.smulLeftCLM ℂ φ ψ) y = 0 := by
    intro y hy
    rw [SchwartzMap.smulLeftCLM_apply_apply hφ_temp]
    rw [hψ y hy, smul_zero]
  rw [hf_eq _ hφψ_supp]
  congr 1
  ext y
  rw [SchwartzMap.smulLeftCLM_apply_apply hφ_temp]
  simp only [smul_eq_mul]
  ring

end DifferentialOperators

namespace DifferentialOperators

/--
[parametrix_smooth_remainder_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma parametrix_smooth_remainder_exists
  {n : ℕ}
  {n}
  {n : ℕ}
  {P : MvPolynomial (Fin n) ℂ}
  {F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hFparam : IsParametrix P F)
  (hFcs : ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧ ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (∀ y, y ∈ K → φ y = 0) → F φ = 0) :
-- imply
  ∃ v w : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ), v + w = u ∧ (∀ y, isSmoothNear v y) := by
-- proof
  set ψ := constCoeffDiffOp n P F - TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n))
  have hψ_smooth : ∀ y, isSmoothNear ψ y := by
    intro y
    rw [IsParametrix, singularSupport] at hFparam
    simp only [Set.eq_empty_iff_forall_notMem, Set.mem_setOf_eq, not_not] at hFparam
    exact hFparam y
  exact ⟨ψ, u - ψ, by abel, hψ_smooth⟩
/-- **Pseudolocal estimate (distributional convolution form).** For any
parametrix `F` with compact d-support, the singular support of `u` is
contained in `singsupp F + singsupp(P(D) u)`. -/
section EllipticHypoelliptic

end DifferentialOperators

namespace DifferentialOperators

/--
[temperateGrowth_inverseFT_contDiff_away](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma temperateGrowth_inverseFT_contDiff_away
  {n : ℕ}
  {n}
  {n : ℕ}
  {Q : EuclideanSpace ℝ (Fin n) → ℂ}
  {F : EuclideanSpace ℝ (Fin n) → ℂ}
  {k : ℕ}
  {ε : ℝ}
-- given
  (hQ : Function.HasTemperateGrowth Q)
  (hF_tg : Function.HasTemperateGrowth F)
  (hF_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), ∫ ξ, Q ξ • (FourierTransformInv.fourierInv φ : EuclideanSpace ℝ (Fin n) → ℂ) ξ = ∫ y, φ y • F y)
  (hε : 0 < ε) :
-- imply
  ∃ (g : EuclideanSpace ℝ (Fin n) → ℂ), ContDiff ℝ k g ∧ ∀ y, ε / 2 < ‖y‖ → g y = F y :=
-- proof
  ⟨F, hF_tg.1.of_le (by exact_mod_cast le_top), fun _ _ => rfl⟩

end DifferentialOperators

namespace DifferentialOperators

/--
[polySymbol_contDiff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma polySymbol_contDiff
  {n : ℕ}
  {n}
  {n : ℕ}
  {P : MvPolynomial (Fin n) ℂ} :
-- imply
  ContDiff ℝ (⊤ : ℕ∞) (polySymbol n P) := by
-- proof
  suffices h : ∀ Q : MvPolynomial (Fin n) ℂ,
    ContDiff ℝ (⊤ : ℕ∞) (fun ξ : EuclideanSpace ℝ (Fin n) =>
      MvPolynomial.eval (fun j => 2 * Real.pi * Complex.I * (ξ j : ℂ)) Q) from h P
  intro Q
  induction Q using MvPolynomial.induction_on with
  | C c =>
    simp only [MvPolynomial.eval_C]
    exact contDiff_const
  | add P Q hP hQ =>
    simp only [map_add]
    exact hP.add hQ
  | mul_X P j hP =>
    simp only [map_mul, MvPolynomial.eval_X]
    have hcoord : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : EuclideanSpace ℝ (Fin n) =>
      2 * ↑Real.pi * Complex.I * (ξ j : ℂ)) := by
      have hx : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : EuclideanSpace ℝ (Fin n) => (ξ j : ℂ)) := by
        have heq : (fun ξ : EuclideanSpace ℝ (Fin n) => (ξ j : ℂ)) =
          (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) ∘ (EuclideanSpace.proj j) := by
          ext ξ; simp [EuclideanSpace.proj, Complex.ofRealCLM]
        rw [heq]
        exact Complex.ofRealCLM.contDiff.comp (ContinuousLinearMap.contDiff _)
      exact contDiff_const.mul hx
    exact hP.mul hcoord

end DifferentialOperators

namespace DifferentialOperators

/--
[contDiffAt_parametrix_symbol_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma contDiffAt_parametrix_symbol_at_zero
  {n : ℕ}
  {n}
  {n : ℕ}
  {m : ℕ}
  {P : MvPolynomial (Fin n) ℂ}
  {φ : EuclideanSpace ℝ (Fin n) → ℂ}
  {ξ₀ : EuclideanSpace ℝ (Fin n)}
-- given
  (hP : IsElliptic n m P)
  (hn : 0 < n)
  (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
  (hφ_supp : HasCompactSupport φ)
  (hφ_eq_one : ∀ ξ : EuclideanSpace ℝ (Fin n), polySymbol n P ξ ≠ 0 ∨ φ ξ = 1)
  (hφ_nhd_zero : ∀ ξ : EuclideanSpace ℝ (Fin n), polySymbol n P ξ = 0 → ∀ᶠ η in nhds ξ, φ η = 1)
  (h_zero : polySymbol n P ξ₀ = 0)
  (h_phi : φ ξ₀ = 1) :
-- imply
  ContDiffAt ℝ (⊤ : ℕ∞) (fun ξ => (1 - φ ξ) * (polySymbol n P ξ)⁻¹) ξ₀ := by
-- proof
  have heq : (fun ξ => (1 - φ ξ) * (polySymbol n P ξ)⁻¹) =ᶠ[nhds ξ₀] (fun _ => (0 : ℂ)) := by
    filter_upwards [hφ_nhd_zero ξ₀ h_zero] with ξ hξ
    simp [hξ]
  exact contDiffAt_const.congr_of_eventuallyEq heq

end DifferentialOperators

namespace DifferentialOperators

/--
[polySymbol_hasTemperateGrowth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma polySymbol_hasTemperateGrowth
  {n : ℕ}
  {n}
  {n : ℕ}
  {P : MvPolynomial (Fin n) ℂ} :
-- imply
  Function.HasTemperateGrowth (polySymbol n P) := by
-- proof
  suffices h : ∀ Q : MvPolynomial (Fin n) ℂ,
    Function.HasTemperateGrowth (fun ξ : EuclideanSpace ℝ (Fin n) =>
      MvPolynomial.eval (fun j => 2 * Real.pi * Complex.I * (ξ j : ℂ)) Q) from h P
  intro Q
  induction Q using MvPolynomial.induction_on with
  | C c =>
    simp only [MvPolynomial.eval_C]
    exact Function.HasTemperateGrowth.const c
  | add P Q hP hQ =>
    simp only [map_add]
    exact hP.add hQ
  | mul_X P j hP =>
    simp only [map_mul, MvPolynomial.eval_X]
    have hcoord : Function.HasTemperateGrowth (fun ξ : EuclideanSpace ℝ (Fin n) =>
      2 * ↑Real.pi * Complex.I * (ξ j : ℂ)) := by
      have hc : Function.HasTemperateGrowth (fun _ : EuclideanSpace ℝ (Fin n) =>
        (2 * ↑Real.pi * Complex.I : ℂ)) := Function.HasTemperateGrowth.const _
      have hx : Function.HasTemperateGrowth (fun ξ : EuclideanSpace ℝ (Fin n) => (ξ j : ℂ)) := by
        have heq : (fun ξ : EuclideanSpace ℝ (Fin n) => (ξ j : ℂ)) =
          (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) ∘ (EuclideanSpace.proj j) := by
          ext ξ; simp [EuclideanSpace.proj, Complex.ofRealCLM]
        rw [heq]
        exact Complex.ofRealCLM.hasTemperateGrowth.comp (EuclideanSpace.proj j).hasTemperateGrowth
      exact hc.mul hx
    exact hP.mul hcoord
set_option maxHeartbeats 400000 in

end DifferentialOperators

namespace DifferentialOperators

/--
[compactSupport_fourierMultiplier_delta_isSmoothNear](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma compactSupport_fourierMultiplier_delta_isSmoothNear
  {n : ℕ}
  {n}
  {n : ℕ}
  {φ : EuclideanSpace ℝ (Fin n) → ℂ}
  {x₀ : EuclideanSpace ℝ (Fin n)}
-- given
  (hφ_temp : Function.HasTemperateGrowth φ)
  (hφ_compact : HasCompactSupport φ)
  (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ) :
-- imply
  isSmoothNear (TemperedDistribution.fourierMultiplierCLM ℂ φ (TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n)))) x₀ := by
-- proof
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, ?_⟩
  let φ_sch : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) := hφ_compact.toSchwartzMap hφ_smooth
  let f_sch : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) := FourierTransformInv.fourierInv φ_sch
  refine ⟨f_sch, f_sch.smooth', fun ψ _ => ?_⟩
  rw [TemperedDistribution.fourierMultiplierCLM_apply_apply, TemperedDistribution.delta_apply]
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul]
  have heq : ∀ v, (SchwartzMap.smulLeftCLM ℂ φ (FourierTransformInv.fourierInv ψ)) v =
    φ v • (FourierTransformInv.fourierInv ψ) v :=
    fun v => SchwartzMap.smulLeftCLM_apply_apply hφ_temp _ v
  simp_rw [heq]
  simp_rw [show ∀ y, ψ y • (f_sch : EuclideanSpace ℝ (Fin n) → ℂ) y =
    (f_sch : EuclideanSpace ℝ (Fin n) → ℂ) y • ψ y from fun y => mul_comm _ _]
  exact (SchwartzMap.integral_fourierInv_smul_eq φ_sch ψ).symm

end DifferentialOperators

namespace DifferentialOperators

/--
[elliptic_parametrix_isParametrix_proof](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma elliptic_parametrix_isParametrix_proof
  {n : ℕ}
  {n}
  {n : ℕ}
  {m : ℕ}
  {P : MvPolynomial (Fin n) ℂ}
  {Q φ : EuclideanSpace ℝ (Fin n) → ℂ}
  {x₀ : EuclideanSpace ℝ (Fin n)}
-- given
  (hP : IsElliptic n m P)
  (hQ : Function.HasTemperateGrowth Q)
  (hφ : Function.HasTemperateGrowth φ)
  (hPt : Function.HasTemperateGrowth (polySymbol n P))
  (hQP : ∀ ξ, Q ξ * polySymbol n P ξ = 1 - φ ξ)
  (hφs : ∀ x₀, isSmoothNear (TemperedDistribution.fourierMultiplierCLM ℂ φ (TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n)))) x₀) :
-- imply
  isSmoothNear (constCoeffDiffOp n P (TemperedDistribution.fourierMultiplierCLM ℂ Q (TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n)))) - TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n))) x₀ := by
-- proof
  set δ₀ := TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n))
  have hcomp : constCoeffDiffOp n P
    (TemperedDistribution.fourierMultiplierCLM ℂ Q δ₀) =
    TemperedDistribution.fourierMultiplierCLM ℂ (Q * polySymbol n P) δ₀ := by
    simp only [constCoeffDiffOp]
    exact TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply hQ hPt δ₀
  have hQP_eq : Q * polySymbol n P = 1 - φ := by
    ext ξ; exact hQP ξ
  have hkey : constCoeffDiffOp n P
    (TemperedDistribution.fourierMultiplierCLM ℂ Q δ₀) - δ₀ =
    -(TemperedDistribution.fourierMultiplierCLM ℂ φ δ₀) := by
    rw [hcomp, hQP_eq]
    have h1φ : Function.HasTemperateGrowth (1 - φ) :=
      (Function.HasTemperateGrowth.const (1 : ℂ)).sub hφ
    ext u
    simp only [TemperedDistribution.fourierMultiplierCLM_apply_apply,
      UniformConvergenceCLM.sub_apply, UniformConvergenceCLM.neg_apply]
    have hsum : SchwartzMap.smulLeftCLM ℂ (1 - φ) (FourierTransformInv.fourierInv u) +
      SchwartzMap.smulLeftCLM ℂ φ (FourierTransformInv.fourierInv u) =
      FourierTransformInv.fourierInv u := by
      ext x
      simp only [SchwartzMap.add_apply]
      rw [SchwartzMap.smulLeftCLM_apply_apply h1φ, SchwartzMap.smulLeftCLM_apply_apply hφ]
      simp [Pi.sub_apply, smul_eq_mul, sub_mul, one_mul, sub_add_cancel]
    have hab : FourierTransform.fourier
      (SchwartzMap.smulLeftCLM ℂ (1 - φ) (FourierTransformInv.fourierInv u)) +
      FourierTransform.fourier
      (SchwartzMap.smulLeftCLM ℂ φ (FourierTransformInv.fourierInv u)) = u := by
      rw [← FourierAdd.fourier_add, hsum, FourierTransform.fourier_fourierInv_eq]
    have hlin : δ₀ (FourierTransform.fourier
      (SchwartzMap.smulLeftCLM ℂ (1 - φ) (FourierTransformInv.fourierInv u))) +
      δ₀ (FourierTransform.fourier
      (SchwartzMap.smulLeftCLM ℂ φ (FourierTransformInv.fourierInv u))) = δ₀ u := by
      rw [← map_add δ₀, hab]
    linear_combination hlin
  rw [hkey]
  obtain ⟨U, hU_open, hx₀_U, f, hf_smooth, hf_eq⟩ := hφs x₀
  exact ⟨U, hU_open, hx₀_U, -f, hf_smooth.neg, fun ψ hψ => by
    simp only [UniformConvergenceCLM.neg_apply, hf_eq ψ hψ, Pi.neg_apply, smul_neg,
      integral_neg]⟩
/-- **Pointwise singular-support bound for an elliptic parametrix.** Any
parametrix `F` for an elliptic operator `P(D)` is smooth at every nonzero
point. Proven by comparing `F` to the explicit Fourier-multiplier
parametrix `F₀ = Q(D) δ₀` via `parametrix_inversion_isSmoothNear`. -/
section PoissonEquation
open Filter Topology

end DifferentialOperators

namespace DifferentialOperators.SmoothZeroAtInfty

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma ext
  {n : ℕ}
  {n}
  {n : ℕ}
  {u v : SmoothZeroAtInfty n}
-- given
  (h : ∀ x, u x = v x) :
-- imply
  u = v :=
-- proof
  DFunLike.ext u v h

end DifferentialOperators.SmoothZeroAtInfty

namespace DifferentialOperators.SmoothZeroAtInfty

/--
[smooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma smooth
  {n : ℕ}
  {n}
  {n : ℕ}
  {u : SmoothZeroAtInfty n} :
-- imply
  ContDiff ℝ (⊤ : ℕ∞) u :=
-- proof
  u.smooth'

end DifferentialOperators.SmoothZeroAtInfty

namespace DifferentialOperators.SmoothZeroAtInfty

/--
[iteratedFDeriv_zero_at_infty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma iteratedFDeriv_zero_at_infty
  {n : ℕ}
  {n}
  {n : ℕ}
  {u : SmoothZeroAtInfty n}
  {m : ℕ} :
-- imply
  Tendsto (fun x => ‖iteratedFDeriv ℝ m u x‖) (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) :=
-- proof
  u.iteratedFDeriv_zero_at_infty' m

end DifferentialOperators.SmoothZeroAtInfty

namespace DifferentialOperators

/--
[contDiff_mvPolynomial_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma contDiff_mvPolynomial_eval
  {n₀ : ℕ}
  {Q : MvPolynomial (Fin n₀) ℝ} :
-- imply
  ContDiff ℝ (⊤ : ℕ∞) (fun ξ : EuclideanSpace ℝ (Fin n₀) => MvPolynomial.eval (fun i => ξ i) Q) := by
-- proof
  induction Q using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.eval_C]; exact contDiff_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp =>
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X]
    exact hp.mul (contDiff_piLp_apply 2)

end DifferentialOperators

namespace DifferentialOperators

/--
[norm_iteratedFDerivWithin_inv_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma norm_iteratedFDerivWithin_inv_eq
  {k : ℕ}
  {y : ℝ}
  {s : Set ℝ}
-- given
  (hs : IsOpen s)
  (hys : y ∈ s) :
-- imply
  ‖iteratedFDerivWithin ℝ k Inv.inv s y‖ = ↑(k.factorial) * ‖y‖⁻¹ ^ (k + 1) := by
-- proof
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  have hfun : Inv.inv = fun z : ℝ => 1 / z := by ext z; exact (one_div z).symm
  rw [hfun, iteratedDerivWithin_one_div k hs hys]
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_natCast]
  congr 1
  rw [show (-1 : ℤ) - ↑k = -(↑(k + 1) : ℤ) by omega]
  rw [zpow_neg, norm_inv, zpow_natCast, norm_pow, one_div, inv_pow]

end DifferentialOperators

namespace DifferentialOperators

/--
[contDiffAt_inv_mvPolynomial_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma contDiffAt_inv_mvPolynomial_eval
  {n₀ : ℕ}
  {P : MvPolynomial (Fin n₀) ℝ}
  {ξ : EuclideanSpace ℝ (Fin n₀)}
-- given
  (hP : MvPolynomial.eval (fun i => ξ i) P ≠ 0) :
-- imply
  ContDiffAt ℝ (⊤ : ℕ∞) (fun ξ' : EuclideanSpace ℝ (Fin n₀) => (MvPolynomial.eval (fun i => ξ' i) P)⁻¹) ξ :=
-- proof
  (contDiff_mvPolynomial_eval P).contDiffAt.inv hP

end DifferentialOperators

namespace DifferentialOperators

/--
[hasFDerivAt_inv_mvPolynomial_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma hasFDerivAt_inv_mvPolynomial_eval
  {n₀ : ℕ}
  {P : MvPolynomial (Fin n₀) ℝ}
  {ξ : EuclideanSpace ℝ (Fin n₀)}
-- given
  (hP : MvPolynomial.eval (fun i => ξ i) P ≠ 0) :
-- imply
  HasFDerivAt (fun ξ' : EuclideanSpace ℝ (Fin n₀) => (MvPolynomial.eval (fun i => ξ' i) P)⁻¹) (-(MvPolynomial.eval (fun i => ξ i) P)⁻¹ ^ 2 • fderiv ℝ (fun ξ' : EuclideanSpace ℝ (Fin n₀) => MvPolynomial.eval (fun i => ξ' i) P) ξ) ξ := by
-- proof
  have hP_diff : HasFDerivAt
    (fun ξ' : EuclideanSpace ℝ (Fin n₀) => MvPolynomial.eval (fun i => ξ' i) P)
    (fderiv ℝ (fun ξ' => MvPolynomial.eval (fun i => ξ' i) P) ξ) ξ :=
    ((contDiff_mvPolynomial_eval P).differentiable (by simp)).differentiableAt.hasFDerivAt
  have h := (hasFDerivAt_inv hP).comp ξ hP_diff
  convert h using 1
  ext v
  simp [ContinuousLinearMap.toSpanSingleton_apply, mul_comm, sq, inv_mul_eq_div]

end DifferentialOperators

namespace DifferentialOperators

/--
[norm_fderiv_inv_mvPolynomial_eval_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma norm_fderiv_inv_mvPolynomial_eval_le
  {n₀ : ℕ}
  {P : MvPolynomial (Fin n₀) ℝ}
  {ξ : EuclideanSpace ℝ (Fin n₀)}
-- given
  (hP : MvPolynomial.eval (fun i => ξ i) P ≠ 0) :
-- imply
  ‖fderiv ℝ (fun ξ' : EuclideanSpace ℝ (Fin n₀) => (MvPolynomial.eval (fun i => ξ' i) P)⁻¹) ξ‖ ≤ ‖fderiv ℝ (fun ξ' : EuclideanSpace ℝ (Fin n₀) => MvPolynomial.eval (fun i => ξ' i) P) ξ‖ / ‖MvPolynomial.eval (fun i => ξ i) P‖ ^ 2 := by
-- proof
  rw [(hasFDerivAt_inv_mvPolynomial_eval P ξ hP).fderiv]
  rw [norm_smul, norm_neg, norm_pow, norm_inv, inv_pow, div_eq_mul_inv, mul_comm]

end DifferentialOperators

namespace DifferentialOperators

/--
[norm_iteratedFDeriv_succ_eq_norm_iteratedFDeriv_fderiv_inv_poly](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma norm_iteratedFDeriv_succ_eq_norm_iteratedFDeriv_fderiv_inv_poly
  {n₀ : ℕ}
  {P : MvPolynomial (Fin n₀) ℝ}
  {k : ℕ}
  {ξ : EuclideanSpace ℝ (Fin n₀)} :
-- imply
  ‖iteratedFDeriv ℝ (k + 1) (fun ξ' : EuclideanSpace ℝ (Fin n₀) => (MvPolynomial.eval (fun i => ξ' i) P)⁻¹) ξ‖ = ‖iteratedFDeriv ℝ k (fderiv ℝ (fun ξ' : EuclideanSpace ℝ (Fin n₀) => (MvPolynomial.eval (fun i => ξ' i) P)⁻¹)) ξ‖ :=
-- proof
  norm_iteratedFDeriv_fderiv.symm
end DifferentialOperators
namespace DifferentialOperators
open MeasureTheory

end DifferentialOperators

namespace DifferentialOperators

/--
[laplacianPoly_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma laplacianPoly_ne_zero
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  laplacianPoly (n := n) ≠ 0 := by
-- proof
  unfold laplacianPoly
  intro h
  have h0 : Fin n := ⟨0, by omega⟩
  let e₀ : Fin n → ℂ := fun j => if j = h0 then 1 else 0
  have heval := congr_arg (MvPolynomial.eval e₀) h
  simp only [map_sum, map_zero, MvPolynomial.eval_pow, MvPolynomial.eval_X] at heval
  have key : (e₀ h0) ^ 2 = 1 := by simp [e₀]
  have hterm : ∑ j : Fin n, (e₀ j) ^ 2 = 1 := by
    have hzero : ∀ j : Fin n, j ≠ h0 → (e₀ j) ^ 2 = 0 := by
      intro j hj; simp [e₀, hj]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ h0)]
    rw [key]
    have : ∑ j ∈ Finset.univ.erase h0, (e₀ j) ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact hzero j (Finset.ne_of_mem_erase hj)
    rw [this]; ring
  exact one_ne_zero (hterm.symm.trans heval)
open Filter Topology

end DifferentialOperators

namespace DifferentialOperators

/--
[schwartz_compSubConstCLM_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma schwartz_compSubConstCLM_continuous
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E]
  [BorelSpace E]
  {ψ : 𝓢(E, ℂ)} :
-- imply
  Continuous (fun x : E => compSubConstCLM ℂ x ψ) := by
-- proof
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [ContinuousAt, (schwartz_withSeminorms ℂ E ℂ).tendsto_nhds]
  intro ⟨k, n⟩ ε hε
  set C := 2 ^ k * (Finset.Iic (k, n + 1)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) ψ
  set Kx := (1 + ‖x₀‖) ^ k * 2 ^ k
  set K := Kx * C
  set δ := min 1 (ε / (K + 1))
  have hδ_pos : 0 < δ := by positivity
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ_pos, fun {x} hx => ?_⟩
  rw [dist_eq_norm] at hx
  have hx1 : ‖x - x₀‖ ≤ 1 := le_trans (le_of_lt hx) (min_le_left _ _)
  show (schwartzSeminormFamily ℂ E ℂ (k, n)) _ < ε
  rw [SchwartzMap.compSubConstCLM_sub_eq ψ x x₀]
  set φ := SchwartzMap.compSubConstCLM ℂ (x - x₀) ψ - ψ
  have hbound := TemperedDistributions.SchwartzMap.seminorm_compSubConst_le ℂ k n φ x₀
  have hsup_bound : ((Finset.Iic (k, n)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2)) φ ≤
    C * ‖x - x₀‖ := by
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro ⟨j, m⟩ hjm
    rw [Finset.mem_Iic] at hjm
    have hj : j ≤ k := hjm.1
    have hm : m ≤ n := hjm.2
    have hsub := SchwartzMap.seminorm_translate_sub_le ψ j m (x - x₀) hx1
    have h2pow : (2 : ℝ) ^ j ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hj
    have hfin_mono : (Finset.Iic (j, m + 1)).sup (fun p => SchwartzMap.seminorm (𝕜 := ℂ) (E := E) (F := ℂ) p.1 p.2) ≤
      (Finset.Iic (k, n + 1)).sup (fun p => SchwartzMap.seminorm (𝕜 := ℂ) (E := E) (F := ℂ) p.1 p.2) := by
      apply Finset.sup_mono
      intro ⟨a, b⟩ hab
      simp only [Finset.mem_Iic] at hab ⊢
      exact ⟨le_trans hab.1 hj, le_trans hab.2 (Nat.succ_le_succ hm)⟩
    calc (SchwartzMap.seminorm ℂ j m) φ
      ≤ 2 ^ j * (Finset.Iic (j, m + 1)).sup (fun p => SchwartzMap.seminorm ℂ p.1 p.2) ψ *
        ‖x - x₀‖ := hsub
      _ ≤ 2 ^ k * (Finset.Iic (k, n + 1)).sup (fun p => SchwartzMap.seminorm ℂ p.1 p.2) ψ *
        ‖x - x₀‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply mul_le_mul h2pow (hfin_mono ψ) (by positivity) (by positivity)
      _ = C * ‖x - x₀‖ := by ring
  calc (schwartzSeminormFamily ℂ E ℂ (k, n)) (SchwartzMap.compSubConstCLM ℂ x₀ φ)
    ≤ Kx * (Finset.Iic (k, n)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) φ := hbound
    _ ≤ Kx * (C * ‖x - x₀‖) := mul_le_mul_of_nonneg_left hsup_bound (by positivity)
    _ < ε := by
      have hK_nonneg : 0 ≤ K := by positivity
      have hK1 : 0 < K + 1 := by positivity
      calc Kx * (C * ‖x - x₀‖)
        ≤ Kx * (C * δ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left (le_of_lt hx) (by positivity)
        _ = K * δ := by ring
        _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hK_nonneg
        _ < ε := by
          have : K / (K + 1) < 1 := by rw [div_lt_one hK1]; linarith
          calc K * (ε / (K + 1)) = (K / (K + 1)) * ε := by ring
            _ < 1 * ε := mul_lt_mul_of_pos_right this hε
            _ = ε := one_mul ε

end DifferentialOperators

namespace DifferentialOperators

/--
[iteratedFDeriv_fderiv_apply_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma iteratedFDeriv_fderiv_apply_eq
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E]
  [BorelSpace E]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  {n : ℕ}
  {f : E → F}
  {y : E}
-- given
  (hf : ContDiff ℝ (↑(n + 1) : WithTop ℕ∞) f)
  (h : E) :
-- imply
  iteratedFDeriv ℝ n (fun z => (fderiv ℝ f z) h) y = (ContinuousLinearMap.apply ℝ F h).compContinuousMultilinearMap (iteratedFDeriv ℝ n (fderiv ℝ f) y) := by
-- proof
  have hfderiv : ContDiffAt ℝ (↑n : WithTop ℕ∞) (fderiv ℝ f) y := by
    have : ContDiff ℝ (↑n + 1 : WithTop ℕ∞) f := by exact_mod_cast hf
    exact (contDiff_succ_iff_fderiv.mp this).2.2.contDiffAt
  exact (ContinuousLinearMap.apply ℝ F h).iteratedFDeriv_comp_left hfderiv le_rfl

end DifferentialOperators

namespace DifferentialOperators

/--
[norm_iteratedFDeriv_fderiv_apply_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma norm_iteratedFDeriv_fderiv_apply_le
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E]
  [BorelSpace E]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  {n : ℕ}
  {f : E → F}
  {y : E}
-- given
  (hf : ContDiff ℝ (↑(n + 1) : WithTop ℕ∞) f)
  (h : E) :
-- imply
  ‖iteratedFDeriv ℝ n (fun z => (fderiv ℝ f z) h) y‖ ≤ ‖iteratedFDeriv ℝ (n + 1) f y‖ * ‖h‖ := by
-- proof
  have hfderiv : ContDiffAt ℝ (↑n : WithTop ℕ∞) (fderiv ℝ f) y := by
    have : ContDiff ℝ (↑n + 1 : WithTop ℕ∞) f := by exact_mod_cast hf
    exact (contDiff_succ_iff_fderiv.mp this).2.2.contDiffAt
  have hle := norm_iteratedFDeriv_clm_apply_const (f := fderiv ℝ f) (c := h) (x := y)
    hfderiv (le_refl _)
  rw [norm_iteratedFDeriv_fderiv] at hle
  linarith [mul_comm ‖h‖ ‖iteratedFDeriv ℝ (n + 1) f y‖]

end DifferentialOperators

namespace DifferentialOperators

/--
[norm_iteratedFDeriv_taylor_remainder_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma norm_iteratedFDeriv_taylor_remainder_le
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E]
  [BorelSpace E]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  {g : E → F}
  {C : ℝ}
-- given
  (hg : ContDiff ℝ 2 g)
  (hC : ∀ z : E, ‖iteratedFDeriv ℝ 2 g z‖ ≤ C)
  (y h : E) :
-- imply
  ‖g (y - h) - g y + (fderiv ℝ g y) h‖ ≤ C * ‖h‖ ^ 2 := by
-- proof
  set Φ : E → F := fun z => g z - g y - (fderiv ℝ g y) (z - y) with hΦ_def
  have hΦy : Φ y = 0 := by simp [hΦ_def, sub_self]
  have hΦyh : Φ (y - h) = g (y - h) - g y + (fderiv ℝ g y) h := by
    simp only [hΦ_def, map_sub]; abel
  have hne2 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hg_diff : Differentiable ℝ g := hg.differentiable hne2
  have hΦ_hasFDeriv : ∀ z, HasFDerivAt Φ (fderiv ℝ g z - fderiv ℝ g y) z := by
    intro z
    have hg_has : HasFDerivAt g (fderiv ℝ g z) z := (hg_diff z).hasFDerivAt
    have h1 : HasFDerivAt (fun w => g w - g y) (fderiv ℝ g z) z := by
      have h := hg_has.sub (hasFDerivAt_const (g y) z); rwa [sub_zero] at h
    have h2 : HasFDerivAt (fun w => (fderiv ℝ g y) (w - y)) (fderiv ℝ g y) z := by
      have hsub : HasFDerivAt (fun w => w - y) (ContinuousLinearMap.id ℝ E) z := by
        have h := (hasFDerivAt_id (𝕜 := ℝ) z).sub (hasFDerivAt_const y z); rwa [sub_zero] at h
      have h := (fderiv ℝ g y).hasFDerivAt.comp z hsub; rwa [ContinuousLinearMap.comp_id] at h
    convert h1.sub h2 using 1
  have hfderiv_g_diff : Differentiable ℝ (fderiv ℝ g) := by
    have hg1 : ContDiff ℝ 1 (fderiv ℝ g) := by
      have : ContDiff ℝ (↑(1 : ℕ) + 1 : WithTop ℕ∞) g := by exact_mod_cast hg
      exact (contDiff_succ_iff_fderiv.mp this).2.2
    exact hg1.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hfderiv_fderiv_bound : ∀ w : E, ‖fderiv ℝ (fderiv ℝ g) w‖ ≤ C := by
    intro w
    have heq : ‖fderiv ℝ (fderiv ℝ g) w‖ = ‖iteratedFDeriv ℝ 2 g w‖ := by
      conv_rhs => rw [show (2 : ℕ) = 1 + 1 from rfl]
      rw [← norm_iteratedFDeriv_fderiv (n := 1),
        ← norm_iteratedFDeriv_fderiv (n := 0) (f := fderiv ℝ g)]
      simp
    linarith [hC w]
  have hinner_mvt : ∀ z : E, ‖fderiv ℝ g z - fderiv ℝ g y‖ ≤ C * ‖z - y‖ := by
    intro z
    have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := Set.univ)
      (fun x _ => hfderiv_g_diff x) (fun x _ => hfderiv_fderiv_bound x)
      convex_univ (Set.mem_univ z) (Set.mem_univ y)
    rwa [norm_sub_rev, norm_sub_rev y z] at hmvt
  have hC_nonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC y)
  have hbound_on_seg :
    ∀ z ∈ segment ℝ y (y - h), ‖fderiv ℝ g z - fderiv ℝ g y‖ ≤ C * ‖h‖ := by
    intro z hz
    have hzy : ‖z - y‖ ≤ ‖h‖ := by
      rw [segment_eq_image' ℝ y (y - h)] at hz
      obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
      simp only [sub_sub_cancel_left]
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0, norm_neg]
      exact mul_le_of_le_one_left (norm_nonneg _) ht1
    calc ‖fderiv ℝ g z - fderiv ℝ g y‖ ≤ C * ‖z - y‖ := hinner_mvt z
      _ ≤ C * ‖h‖ := mul_le_mul_of_nonneg_left hzy hC_nonneg
  have houter := (convex_segment y (y - h)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f' := fun z => fderiv ℝ g z - fderiv ℝ g y)
    (fun z hz => (hΦ_hasFDeriv z).hasFDerivWithinAt)
    hbound_on_seg
    (left_mem_segment ℝ y (y - h))
    (right_mem_segment ℝ y (y - h))
  rw [hΦyh, hΦy, sub_zero] at houter
  calc ‖g (y - h) - g y + (fderiv ℝ g y) h‖
    ≤ C * ‖h‖ * ‖y - h - y‖ := houter
    _ = C * ‖h‖ * ‖h‖ := by rw [sub_sub_cancel_left, norm_neg]
    _ = C * ‖h‖ ^ 2 := by ring

end DifferentialOperators

namespace DifferentialOperators

/--
[HasCompactDsupport.isVanishingOn_complement](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma HasCompactDsupport.isVanishingOn_complement
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E]
  [BorelSpace E]
  {v : 𝓢'(E, ℂ)}
-- given
  (hv : HasCompactDsupport v) :
-- imply
  ∃ (K : Set E), IsCompact K ∧ Distribution.IsVanishingOn v Kᶜ := by
-- proof
  refine ⟨dsupport v, hv, ?_⟩
  intro ψ hψ_supp
  suffices h_cs : ∀ (φ : 𝓢(E, ℂ)), HasCompactSupport φ →
    tsupport (⇑φ) ⊆ (dsupport v)ᶜ → v φ = 0 by
    have hclosed : IsClosed {φ : 𝓢(E, ℂ) | v φ = 0} :=
      isClosed_eq v.cont continuous_const
    have hmem : ψ ∈ closure {φ : 𝓢(E, ℂ) | v φ = 0} := by
      apply mem_closure_of_tendsto (f := fun m => bumpCutoffMul m ψ) (b := Filter.atTop)
      · rw [(schwartz_withSeminorms ℂ E ℂ).tendsto_nhds _ ψ]
        intro ⟨k, j⟩ ε hε
        have h := seminorm_cutoff_sub_tendsto ℂ ψ k j
        rw [Metric.tendsto_atTop] at h
        obtain ⟨N, hN⟩ := h ε hε
        filter_upwards [Filter.Ici_mem_atTop N] with m hm
        simp only [SchwartzMap.schwartzSeminormFamily_apply]
        have h1 := hN m hm
        rw [Real.dist_0_eq_abs, abs_of_nonneg (apply_nonneg _ _)] at h1
        calc (SchwartzMap.seminorm ℂ k j) (bumpCutoffMul m ψ - ψ)
          = (SchwartzMap.seminorm ℂ k j) (ψ - bumpCutoffMul m ψ) := by
            rw [← map_neg_eq_map]; congr 1; abel
          _ < ε := h1
      · apply Filter.Eventually.of_forall
        intro m
        have hts : tsupport (⇑(bumpCutoffMul m ψ)) ⊆ tsupport (⇑ψ) := by
          apply closure_mono
          intro x hx
          rw [Function.mem_support] at hx ⊢
          intro hψx
          apply hx
          rw [bumpCutoffMul_apply, hψx, smul_zero]
        exact h_cs _ (bumpCutoffMul_hasCompactSupport m ψ) (hts.trans hψ_supp)
    exact hclosed.closure_subset hmem
  classical
  intro φ hφ_compact hφ_supp
  have hclosed_dsupp : IsClosed (dsupport v) := isClosed_dsupport
  let U : E → Set E := fun x =>
    if hx : x ∈ dsupport v then (tsupport (⇑φ))ᶜ
    else (notMem_dsupport_iff x |>.mp hx).choose
  have hU_open : ∀ x, IsOpen (U x) := by
    intro x
    simp only [U]
    split_ifs with hx
    · exact isOpen_compl_iff.mpr (isClosed_tsupport (⇑φ))
    · exact (notMem_dsupport_iff x |>.mp hx).choose_spec.2.1
  have hU_mem : ∀ x, x ∈ U x := by
    intro x
    simp only [U]
    split_ifs with hx
    · exact Set.mem_compl (fun hxφ => absurd hx (hφ_supp hxφ))
    · exact (notMem_dsupport_iff x |>.mp hx).choose_spec.2.2
  have hU_vanish_or_disjoint : ∀ x, IsVanishingOn (⇑v) (U x) ∨ U x ⊆ (tsupport (⇑φ))ᶜ := by
    intro x
    simp only [U]
    split_ifs with hx
    · right; exact Set.Subset.rfl
    · left; exact (notMem_dsupport_iff x |>.mp hx).choose_spec.1
  have hcov : Set.univ ⊆ ⋃ x, U x := fun x _ => Set.mem_iUnion.mpr ⟨x, hU_mem x⟩
  obtain ⟨ρ, hρ_sub⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ E) isClosed_univ U hU_open hcov
  have hlf := ρ.locallyFinite
  have hfin : {i | (Function.support (⇑(ρ i)) ∩ tsupport (⇑φ)).Nonempty}.Finite :=
    hlf.finite_nonempty_inter_compact hφ_compact
  set s := hfin.toFinset with hs_def
  have hρ_smooth : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (ρ i : E → ℝ) := by
    intro i; rw [← contMDiff_iff_contDiff]; exact (ρ i).contMDiff
  have hprod_cs : ∀ i, HasCompactSupport (fun x => (↑(ρ i x) : ℂ) * φ x) :=
    fun i => hφ_compact.mul_left
  have hprod_smooth : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (↑(ρ i x) : ℂ) * φ x) :=
    fun i => (Complex.ofRealCLM.contDiff.comp (hρ_smooth i)).mul (φ.smooth ⊤)
  let g : E → 𝓢(E, ℂ) := fun i => (hprod_cs i).toSchwartzMap (hprod_smooth i)
  have hg_vanish : ∀ i, v (g i) = 0 := by
    intro i
    cases hU_vanish_or_disjoint i with
    | inl h_van =>
      apply h_van
      calc tsupport ⇑(g i) ⊆ tsupport (ρ i : E → ℝ) := by
        apply closure_mono
        intro x hx
        rw [Function.mem_support] at hx ⊢
        intro hρx; apply hx; rw [(hprod_cs i).toSchwartzMap_toFun (hprod_smooth i)]
        simp [hρx]
        _ ⊆ U i := hρ_sub i
    | inr h_disj =>
      have hg_zero : ∀ x, (g i) x = 0 := by
        intro x
        rw [(hprod_cs i).toSchwartzMap_toFun (hprod_smooth i)]
        by_cases hρ : (ρ i) x = 0
        · simp [hρ]
        ·
          have hx_not_supp : x ∉ tsupport (⇑φ) := by
            have : x ∈ tsupport (ρ i : E → ℝ) :=
              subset_tsupport _ (Function.mem_support.mpr hρ)
            exact h_disj (hρ_sub i this)
          have : φ x = 0 := by
            by_contra h
            exact hx_not_supp (subset_tsupport _ (Function.mem_support.mpr h))
          simp [this]
      have : (g i : 𝓢(E, ℂ)) = 0 := by ext x; exact hg_zero x
      rw [this, map_zero]
  have hφ_eq : φ = ∑ i ∈ s, g i := by
    ext x
    have hsum_app : (∑ i ∈ s, g i) x = ∑ i ∈ s, (g i) x := by
      change (⇑(∑ i ∈ s, g i)) x = _
      simp
    rw [hsum_app]
    have heq : ∀ i, (g i) x = (↑(ρ i x) : ℂ) * φ x :=
      fun i => (hprod_cs i).toSchwartzMap_toFun (hprod_smooth i) x
    simp_rw [heq, ← Finset.sum_mul]
    by_cases hφx : φ x = 0
    · simp [hφx]
    · have hx_supp : x ∈ tsupport (⇑φ) := subset_tsupport _ (Function.mem_support.mpr hφx)
      have hρ_zero : ∀ i, i ∉ s → (ρ i) x = 0 := by
        intro i hi
        by_contra h
        exact hi (hs_def ▸ hfin.mem_toFinset.mpr ⟨x, Function.mem_support.mpr h, hx_supp⟩)
      have hsum_one : ∑ᶠ i, (ρ i) x = 1 := ρ.sum_eq_one (Set.mem_univ x)
      have hsupp : Function.support (fun i => (ρ i) x) ⊆ ↑s := by
        intro i hi
        rw [Finset.mem_coe]
        by_contra hi'
        exact (Function.mem_support.mp hi) (hρ_zero i hi')
      rw [finsum_eq_sum_of_support_subset _ hsupp] at hsum_one
      have hcsum : (∑ i ∈ s, (↑(ρ i x) : ℂ)) = 1 := by
        rw [← Complex.ofReal_one, ← hsum_one]
        simp
      rw [hcsum, one_mul]
  rw [hφ_eq, map_sum]
  exact Finset.sum_eq_zero (fun i _ => hg_vanish i)

end DifferentialOperators

namespace DifferentialOperators

/--
[cutoffMul_apply_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma cutoffMul_apply_eq
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E]
  [BorelSpace E]
  {χ : E → ℝ}
  {f : 𝓢(E, ℂ)}
  {y : E}
-- given
  (hχcs : HasCompactSupport χ)
  (hχcd : ContDiff ℝ ⊤ χ) :
-- imply
  (cutoffMul χ hχcs hχcd f) y = χ y • f y := by
-- proof
  unfold cutoffMul
  simp only [HasCompactSupport.toSchwartzMap_toFun]
  exact Complex.real_smul

end DifferentialOperators

namespace DifferentialOperators

/--
[cutoffMul_coe_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma cutoffMul_coe_eq
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E]
  [BorelSpace E]
  {χ : E → ℝ}
  {f : 𝓢(E, ℂ)}
-- given
  (hχcs : HasCompactSupport χ)
  (hχcd : ContDiff ℝ ⊤ χ) :
-- imply
  ⇑(cutoffMul χ hχcs hχcd f) = fun y => χ y • f y :=
-- proof
  funext (cutoffMul_apply_eq χ hχcs hχcd f)

end DifferentialOperators

namespace DifferentialOperators

/--
[seminorm_compSubConst_zero_weight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma seminorm_compSubConst_zero_weight
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E]
  [BorelSpace E]
  {x : E}
  {φ : 𝓢(E, ℂ)}
  {m : ℕ} :
-- imply
  SchwartzMap.seminorm ℂ 0 m (compSubConstCLM ℂ x φ) = SchwartzMap.seminorm ℂ 0 m φ := by
-- proof
  apply le_antisymm
  · apply SchwartzMap.seminorm_le_bound ℂ 0 m _ (apply_nonneg _ _)
    intro y
    simp only [pow_zero, one_mul]
    have hc : ⇑(compSubConstCLM ℂ x φ) = fun z => φ (z - x) := by
      ext z; simp [compSubConstCLM_apply]
    rw [hc, iteratedFDeriv_comp_sub]
    have h := le_seminorm ℂ 0 m φ (y - x)
    simp only [pow_zero, one_mul] at h; exact h
  · apply SchwartzMap.seminorm_le_bound ℂ 0 m _ (apply_nonneg _ _)
    intro y
    simp only [pow_zero, one_mul]
    have hc : ⇑(compSubConstCLM ℂ x φ) = fun z => φ (z - x) := by
      ext z; simp [compSubConstCLM_apply]
    have h := le_seminorm ℂ 0 m (compSubConstCLM ℂ x φ) (y + x)
    simp only [pow_zero, one_mul] at h
    rwa [hc, iteratedFDeriv_comp_sub, add_sub_cancel_right] at h
omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
set_option maxHeartbeats 6400000 in

end DifferentialOperators

namespace DifferentialOperators

/--
[cutoff_translation_seminorm_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma cutoff_translation_seminorm_bound
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E]
  [BorelSpace E]
  {χ : E → ℝ}
  {k n : ℕ}
-- given
  (hχcs : HasCompactSupport χ)
  (hχcd : ContDiff ℝ ⊤ χ) :
-- imply
  ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (φ : 𝓢(E, ℂ)) (x : E), SchwartzMap.seminorm ℂ k n (cutoffMul χ hχcs hχcd (compSubConstCLM ℂ x φ)) ≤ C * (s.sup (schwartzSeminormFamily ℂ E ℂ)) φ := by
-- proof
  let s : Finset (ℕ × ℕ) := (Finset.range (n + 1)).image (fun j => (0, j))
  have hRk : ∃ Rk : ℝ, 0 ≤ Rk ∧ ∀ y ∈ tsupport χ, ‖y‖ ^ k ≤ Rk := by
    by_cases hne : (tsupport χ).Nonempty
    · obtain ⟨y₀, _, hmax⟩ := hχcs.isCompact.exists_isMaxOn hne
      (continuous_norm.pow k).continuousOn
      exact ⟨‖y₀‖ ^ k, by positivity, fun y hy => hmax hy⟩
    · exact ⟨0, le_refl 0, fun y hy =>
      ((Set.not_nonempty_iff_eq_empty.mp hne) ▸ hy).elim⟩
  obtain ⟨Rk, hRk_nn, hRk_bd⟩ := hRk
  have hBi : ∀ i ∈ Finset.range (n + 1),
    ∃ Bi : ℝ, 0 ≤ Bi ∧ ∀ y : E,
    (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖ ≤ Bi := by
    intro i _
    have hcsi : HasCompactSupport (iteratedFDeriv ℝ i χ) := hχcs.iteratedFDeriv i
    have hci : Continuous (iteratedFDeriv ℝ i χ) :=
      (hχcd.of_le le_top).continuous_iteratedFDeriv (by exact_mod_cast le_top)
    by_cases hne : (tsupport (iteratedFDeriv ℝ i χ)).Nonempty
    · obtain ⟨z₀, _, hmax⟩ := hcsi.isCompact.exists_isMaxOn hne
      (continuous_norm.comp hci).continuousOn
      refine ⟨(n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ z₀‖, by positivity, fun y => ?_⟩
      gcongr
      by_cases hy : y ∈ tsupport (iteratedFDeriv ℝ i χ)
      · exact hmax hy
      · have : iteratedFDeriv ℝ i χ y = 0 := by
        have : y ∉ Function.support (iteratedFDeriv ℝ i χ) :=
          fun h => hy (subset_tsupport _ h)
        rwa [Function.mem_support, not_not] at this
        simp [this]
    · exact ⟨0, le_refl 0, fun y => by
      rw [Set.not_nonempty_iff_eq_empty] at hne
      have : iteratedFDeriv ℝ i χ y = 0 := by
        have : y ∉ Function.support (iteratedFDeriv ℝ i χ) := by
          intro h; exact (hne ▸ subset_tsupport _ h).elim
        rwa [Function.mem_support, not_not] at this
      simp [this]⟩
  have hBi_exists : ∀ i ∈ Finset.range (n + 1), ∃ B : ℝ, 0 ≤ B ∧
    ∀ y : E, (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖ ≤ B := hBi
  let Bi' : ℕ → ℝ := fun i =>
    if h : i ∈ Finset.range (n + 1) then (hBi_exists i h).choose else 0
  have hBi'_nn : ∀ i, 0 ≤ Bi' i := by
    intro i; simp only [Bi']; split_ifs with h
    · exact (hBi_exists i h).choose_spec.1
    · exact le_refl 0
  have hBi'_bd : ∀ i ∈ Finset.range (n + 1), ∀ y : E,
    (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖ ≤ Bi' i := by
    intro i hi y; simp only [Bi', dif_pos hi]
    exact (hBi_exists i hi).choose_spec.2 y
  let Ctotal : ℝ := Rk * ∑ i ∈ Finset.range (n + 1), Bi' i
  refine ⟨s, Ctotal, ?_, fun φ x => ?_⟩
  · apply mul_nonneg hRk_nn
    exact Finset.sum_nonneg fun i _ => hBi'_nn i
  apply SchwartzMap.seminorm_le_bound ℂ k n
  · exact mul_nonneg (mul_nonneg hRk_nn
    (Finset.sum_nonneg fun i _ => hBi'_nn i)) (apply_nonneg _ _)
  intro y
  rw [cutoffMul_coe_eq]
  set ψ := compSubConstCLM ℂ x φ
  have hχ_cd : ContDiff ℝ ((↑n : ℕ∞) : WithTop ℕ∞) χ := hχcd.of_le le_top
  have hψ_cd : ContDiff ℝ ((↑n : ℕ∞) : WithTop ℕ∞) ψ := by
    apply ψ.smooth'.of_le; exact_mod_cast le_top
  have hsmul_le := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) hχ_cd hψ_cd y le_rfl
  by_cases hy_supp : y ∈ tsupport χ
  ·
    calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun z => χ z • ψ z) y‖
      ≤ ‖y‖ ^ k * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖ *
        ‖iteratedFDeriv ℝ (n - i) (⇑ψ) y‖ := by
        exact mul_le_mul_of_nonneg_left hsmul_le (by positivity)
      _ = ∑ i ∈ Finset.range (n + 1),
        ‖y‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖) *
        ‖iteratedFDeriv ℝ (n - i) (⇑ψ) y‖ := by
        rw [Finset.mul_sum]; congr 1; ext i; ring
      _ ≤ ∑ i ∈ Finset.range (n + 1),
        Rk * Bi' i * SchwartzMap.seminorm ℂ 0 (n - i) φ := by
        apply Finset.sum_le_sum; intro i hi
        have h1 : ‖y‖ ^ k ≤ Rk := hRk_bd y hy_supp
        have h2 : (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖ ≤ Bi' i := hBi'_bd i hi y
        have h3 : ‖iteratedFDeriv ℝ (n - i) (⇑ψ) y‖ ≤ SchwartzMap.seminorm ℂ 0 (n - i) φ :=
          calc ‖iteratedFDeriv ℝ (n - i) (⇑ψ) y‖
            ≤ SchwartzMap.seminorm ℂ 0 (n - i) ψ :=
              SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ ψ (n - i) y
            _ = SchwartzMap.seminorm ℂ 0 (n - i) φ :=
              seminorm_compSubConst_zero_weight x φ (n - i)
        exact mul_le_mul (mul_le_mul h1 h2 (by positivity) hRk_nn)
          h3 (norm_nonneg _) (mul_nonneg hRk_nn (hBi'_nn i))
      _ ≤ ∑ i ∈ Finset.range (n + 1),
        Rk * Bi' i * (s.sup (schwartzSeminormFamily ℂ E ℂ)) φ := by
        apply Finset.sum_le_sum; intro i hi
        apply mul_le_mul_of_nonneg_left
        · have hmem : (0, n - i) ∈ s :=
          Finset.mem_image.mpr ⟨n - i, Finset.mem_range.mpr (by omega), rfl⟩
          rw [← SchwartzMap.schwartzSeminormFamily_apply ℂ E ℂ 0 (n - i)]
          exact (Finset.le_sup hmem : schwartzSeminormFamily ℂ E ℂ (0, n - i) ≤ _) φ
        · exact mul_nonneg hRk_nn (hBi'_nn i)
      _ = Ctotal * (s.sup (schwartzSeminormFamily ℂ E ℂ)) φ := by
        simp only [Ctotal, Finset.mul_sum]; rw [Finset.sum_mul]
  ·
    have hχ_zero : ∀ i : ℕ, iteratedFDeriv ℝ i χ y = 0 := by
      intro i
      have h1 : y ∉ tsupport (iteratedFDeriv ℝ i χ) :=
        fun h => hy_supp (tsupport_iteratedFDeriv_subset i h)
      have h2 : y ∉ Function.support (iteratedFDeriv ℝ i χ) :=
        fun h => h1 (subset_tsupport _ h)
      rwa [Function.mem_support, not_not] at h2
    calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun z => χ z • ψ z) y‖
      ≤ ‖y‖ ^ k * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖ *
        ‖iteratedFDeriv ℝ (n - i) (⇑ψ) y‖ := by
        exact mul_le_mul_of_nonneg_left hsmul_le (by positivity)
      _ = ‖y‖ ^ k * 0 := by
        congr 1; apply Finset.sum_eq_zero; intro i _; simp [hχ_zero i]
      _ ≤ Ctotal * (s.sup (schwartzSeminormFamily ℂ E ℂ)) φ := by
        simp only [mul_zero]
        exact mul_nonneg (mul_nonneg hRk_nn
          (Finset.sum_nonneg fun i _ => hBi'_nn i)) (apply_nonneg _ _)

end DifferentialOperators

namespace DifferentialOperators

/--
[add_pow_nonneg_le_one_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma add_pow_nonneg_le_one_add
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E]
  [BorelSpace E]
  {a : ℝ}
  {N : ℕ}
-- given
  (ha : 0 ≤ a) :
-- imply
  a + a ^ N ≤ 1 + a ^ (N + 1) := by
-- proof
  suffices h : 0 ≤ (a - 1) * (a ^ N - 1) by nlinarith [pow_succ a N]
  by_cases h : a ≤ 1
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [pow_le_one₀ ha h (n := N)])
  · push Not at h
    exact mul_nonneg (by linarith) (by linarith [one_le_pow₀ h.le (n := N)])

end DifferentialOperators

namespace DifferentialOperators

/--
[one_add_pow_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma one_add_pow_bound
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E]
  [BorelSpace E]
  {a : ℝ}
  {N : ℕ}
-- given
  (ha : 0 ≤ a) :
-- imply
  (1 + a) ^ N ≤ 2 ^ N * (1 + a ^ N) := by
-- proof
  induction N with
  | zero => simp
  | succ N ih =>
    calc (1 + a) ^ (N + 1) = (1 + a) ^ N * (1 + a) := pow_succ _ _
      _ ≤ 2 ^ N * (1 + a ^ N) * (1 + a) := by gcongr
      _ = 2 ^ N * (1 + a + a ^ N + a ^ N * a) := by ring
      _ = 2 ^ N * (1 + a + a ^ N + a ^ (N + 1)) := by rw [pow_succ]
      _ ≤ 2 ^ N * (2 * (1 + a ^ (N + 1))) := by
        gcongr; linarith [add_pow_nonneg_le_one_add a ha N]
      _ = 2 ^ (N + 1) * (1 + a ^ (N + 1)) := by ring
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Rapid decay of `v ∗ φ`.** For `v` with compact `dsupport`, all
iterated derivatives of `x ↦ v(φ(· - x))` decay faster than any
polynomial. Stated with weight `(1 + ‖x‖)^N`. -/
section PolynomialGrowthBound
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end DifferentialOperators

namespace DifferentialOperators

/--
[EuclideanSpace.abs_coord_le_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma EuclideanSpace.abs_coord_le_norm
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E]
  [BorelSpace E]
  {m : ℕ}
  {ξ : EuclideanSpace ℝ (Fin m)}
  {i : Fin m} :
-- imply
  |ξ i| ≤ ‖ξ‖ := by
-- proof
  have h1 : (ξ i) ^ 2 ≤ ∑ j : Fin m, (ξ j) ^ 2 :=
    Finset.single_le_sum (f := fun j => (ξ j) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have h2 : ‖ξ‖ ^ 2 = ∑ j : Fin m, (ξ j) ^ 2 := EuclideanSpace.real_norm_sq_eq ξ
  have h3 : (ξ i) ^ 2 ≤ ‖ξ‖ ^ 2 := by linarith
  exact abs_le_of_sq_le_sq h3 (norm_nonneg ξ)

end DifferentialOperators

namespace DifferentialOperators

/--
[mvPolynomial_eval_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma mvPolynomial_eval_bound
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E]
  [BorelSpace E]
  {n : ℕ}
  {Q : MvPolynomial (Fin n) ℝ} :
-- imply
  ∃ C : ℝ, C > 0 ∧ ∀ ξ : EuclideanSpace ℝ (Fin n), ‖MvPolynomial.eval (fun i => ξ i) Q‖ ≤ C * (1 + ‖ξ‖) ^ Q.totalDegree := by
-- proof
  refine ⟨max 1 (∑ d ∈ Q.support, |Q.coeff d|), by positivity, fun ξ => ?_⟩
  set f : Fin n → ℝ := fun i => ξ i
  have heval : MvPolynomial.eval f Q = ∑ d ∈ Q.support, Q.coeff d * ∏ i : Fin n, f i ^ d i :=
    MvPolynomial.eval_eq' f Q
  rw [heval]
  have h1le : 1 ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
  have hnle : ‖ξ‖ ≤ 1 + ‖ξ‖ := le_add_of_nonneg_left (by norm_num)
  have hmono : ∀ d ∈ Q.support,
    ‖Q.coeff d * ∏ i : Fin n, f i ^ d i‖ ≤
      |Q.coeff d| * (1 + ‖ξ‖) ^ Q.totalDegree := by
    intro d hd
    rw [Real.norm_eq_abs, abs_mul]
    have hprod_bound : |∏ i : Fin n, f i ^ d i| ≤ (1 + ‖ξ‖) ^ Q.totalDegree := by
      rw [Finset.abs_prod]
      have step1 : ∀ i : Fin n, |f i ^ d i| ≤ ‖ξ‖ ^ d i := by
        intro i; rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (EuclideanSpace.abs_coord_le_norm ξ i) _
      have step2 : ∏ i : Fin n, |f i ^ d i| ≤ ∏ i : Fin n, ‖ξ‖ ^ d i :=
        Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => step1 i)
      have step3 : ∏ i : Fin n, ‖ξ‖ ^ d i = ‖ξ‖ ^ ∑ i : Fin n, d i :=
        Finset.prod_pow_eq_pow_sum _ _ _
      have step4 : ∑ i : Fin n, d i ≤ Q.totalDegree := by
        have h := MvPolynomial.le_totalDegree hd
        rw [Finsupp.sum_fintype] at h
        · exact h
        · intros; rfl
      calc ∏ i : Fin n, |f i ^ d i|
        ≤ ‖ξ‖ ^ ∑ i : Fin n, d i := step3 ▸ step2
        _ ≤ (1 + ‖ξ‖) ^ ∑ i : Fin n, d i :=
          pow_le_pow_left₀ (norm_nonneg _) hnle _
        _ ≤ (1 + ‖ξ‖) ^ Q.totalDegree :=
          pow_le_pow_right₀ h1le step4
    exact mul_le_mul_of_nonneg_left hprod_bound (abs_nonneg _)
  calc ‖∑ d ∈ Q.support, Q.coeff d * ∏ i : Fin n, f i ^ d i‖
    ≤ ∑ d ∈ Q.support, ‖Q.coeff d * ∏ i : Fin n, f i ^ d i‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Q.support, (|Q.coeff d| * (1 + ‖ξ‖) ^ Q.totalDegree) :=
      Finset.sum_le_sum hmono
    _ = (∑ d ∈ Q.support, |Q.coeff d|) * (1 + ‖ξ‖) ^ Q.totalDegree :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ max 1 (∑ d ∈ Q.support, |Q.coeff d|) * (1 + ‖ξ‖) ^ Q.totalDegree := by
      apply mul_le_mul_of_nonneg_right (le_max_right _ _)
      positivity
section ParametrixSymbol
open Function MvPolynomial

end DifferentialOperators

namespace DifferentialOperators

/--
[compactSupport_contDiff_to_schwartz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean)
-/
@[path]
lemma compactSupport_contDiff_to_schwartz
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E]
  [BorelSpace E]
  {n : ℕ}
  {φ : EuclideanSpace ℝ (Fin n) → ℂ}
-- given
  (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
  (hφ_supp : HasCompactSupport φ) :
-- imply
  ∃ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), ∀ ξ, (ψ : EuclideanSpace ℝ (Fin n) → ℂ) ξ = φ ξ :=
-- proof
  ⟨hφ_supp.toSchwartzMap hφ_smooth,
    fun ξ => hφ_supp.toSchwartzMap_toFun hφ_smooth ξ⟩
/-- **Existence of a parametrix cutoff.** For an elliptic polynomial `P`,
there is a smooth compactly-supported function `φ` equal to `1` exactly on
the (compact) zero set of the symbol `polySymbol n P`. -/

end DifferentialOperators


-- created on 2026-10-23
