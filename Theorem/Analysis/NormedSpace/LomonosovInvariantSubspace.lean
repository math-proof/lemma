/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap


namespace FunctionalAnalysis.LomonosovInvariantSubspaceWanted

/-- Eigenspace of a nonzero compact operator on an infinite-dimensional space is never `⊤`
(N1: a nonzero compact operator is not a scalar). -/
theorem lomo_eigenspace_ne_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (hInf : ¬ FiniteDimensional ℂ E)
    (K : E →L[ℂ] E) (hK_compact : IsCompactOperator K) (hK_ne : K ≠ 0)
    (μ : ℂ) : Module.End.eigenspace (↑K : Module.End ℂ E) μ ≠ ⊤ := by
  intro htop
  have hKe : ∀ x : E, K x = μ • x := by
    intro x
    have hx : x ∈ Module.End.eigenspace (↑K : Module.End ℂ E) μ := htop ▸ Submodule.mem_top
    simp only [Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe] at hx
    exact hx
  by_cases hμ : μ = 0
  · subst hμ
    apply hK_ne
    ext x
    simp [hKe x]
  · have hfun : (μ⁻¹ • (K : E → E)) = id := by
      funext x
      simp [hKe x, smul_smul, inv_mul_cancel₀ hμ]
    have hcomp : IsCompactOperator (μ⁻¹ • (K : E → E)) := hK_compact.smul μ⁻¹
    rw [hfun] at hcomp
    exact hInf (FiniteDimensional.of_isCompactOperator_id hcomp)

/-- Eigenspaces are invariant under commuting operators. -/
theorem lomo_eigenspace_mapsTo_of_commute
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K T : E →L[ℂ] E) (hComm : T.comp K = K.comp T)
    (μ : ℂ) (x : E) (hx : x ∈ Module.End.eigenspace (↑K : Module.End ℂ E) μ) :
    T x ∈ Module.End.eigenspace (↑K : Module.End ℂ E) μ := by
  simp only [Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe] at hx ⊢
  have hTK : ∀ z : E, K (T z) = T (K z) := by
    intro z
    have h := congrArg (· z) hComm
    simpa [ContinuousLinearMap.comp_apply] using h.symm
  rw [hTK, hx, map_smul]

/-- Case A: if `K` has an eigenvalue, its eigenspace is the wanted subspace. -/
theorem lomo_exists_of_hasEigenvalue
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (hInf : ¬ FiniteDimensional ℂ E)
    (K : E →L[ℂ] E) (hK_compact : IsCompactOperator K) (hK_ne : K ≠ 0)
    (T : E →L[ℂ] E) (hComm : T.comp K = K.comp T)
    (μ : ℂ) (hμ : Module.End.HasEigenvalue (↑K : Module.End ℂ E) μ) :
    ∃ (M : Submodule ℂ E), M ≠ ⊥ ∧ M ≠ ⊤ ∧ IsClosed (M : Set E) ∧ ∀ x ∈ M, T x ∈ M := by
  refine ⟨Module.End.eigenspace (↑K : Module.End ℂ E) μ, hμ, ?_, inferInstance, ?_⟩
  · exact lomo_eigenspace_ne_top hInf K hK_compact hK_ne μ
  · intro x hx
    exact lomo_eigenspace_mapsTo_of_commute K T hComm μ x hx

/-- A compact operator with no nonzero eigenvalue is quasinilpotent. -/
theorem lomo_spectralRadius_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (K : E →L[ℂ] E) (hK_compact : IsCompactOperator K)
    (hno : ∀ μ : ℂ, μ ≠ 0 → ¬ Module.End.HasEigenvalue (↑K : Module.End ℂ E) μ) :
    spectralRadius ℂ K = 0 := by
  rw [spectralRadius_eq_of_unital]
  refine le_antisymm ?_ zero_le
  apply iSup₂_le
  intro k hk
  by_cases hk0 : k = 0
  · subst hk0
    simp
  · exact absurd ((hK_compact.hasEigenvalue_iff_mem_spectrum hk0).mpr hk) (hno k hk0)

/-- Powers of a quasinilpotent decay against any geometric constant. -/
theorem lomo_tendsto_const_pow_mul_norm_pow
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (a : A) (ha : spectralRadius ℂ a = 0)
    (c : ℝ) (hc : 0 ≤ c) :
    Filter.Tendsto (fun m : ℕ => c ^ m * ‖a ^ m‖) Filter.atTop (nhds 0) := by
  have hG := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a
  rw [ha] at hG
  set ε : ℝ := 1 / (2 * (c + 1)) with hε
  have hc1 : (0 : ℝ) < c + 1 := by linarith
  have hεpos : (0 : ℝ) < ε := by positivity
  have hlt : (0 : ENNReal) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hεpos
  have hev := hG.eventually (Iio_mem_nhds hlt)
  have hev2 : ∀ᶠ m : ℕ in Filter.atTop, ‖a ^ m‖ ^ (1 / (m : ℝ)) < ε := by
    filter_upwards [hev] with m hm
    exact (ENNReal.ofReal_lt_ofReal_iff hεpos).mp hm
  have hce : c * ε ≤ 1 / 2 := by
    have hpos : (0 : ℝ) < 2 * (c + 1) := by positivity
    rw [hε, mul_one_div, div_le_iff₀ hpos]
    have h2 : (1 / 2 : ℝ) * (2 * (c + 1)) = c + 1 := by ring
    linarith
  have hbound : ∀ᶠ m : ℕ in Filter.atTop, c ^ m * ‖a ^ m‖ ≤ (1 / 2) ^ m := by
    filter_upwards [hev2, Filter.eventually_gt_atTop 0] with m hm h1m
    have hm0 : m ≠ 0 := by omega
    have hpow : ‖a ^ m‖ = (‖a ^ m‖ ^ (1 / (m : ℝ))) ^ m := by
      rw [one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) hm0]
    have hltm : (‖a ^ m‖ ^ (1 / (m : ℝ))) ^ m < ε ^ m :=
      pow_lt_pow_left₀ hm (Real.rpow_nonneg (norm_nonneg _) _) hm0
    calc c ^ m * ‖a ^ m‖
        = c ^ m * ((‖a ^ m‖ ^ (1 / (m : ℝ))) ^ m) := by conv_lhs => rw [hpow]
      _ ≤ c ^ m * ε ^ m :=
          mul_le_mul_of_nonneg_left hltm.le (pow_nonneg hc _)
      _ = (c * ε) ^ m := by rw [mul_pow]
      _ ≤ (1 / 2) ^ m :=
          pow_le_pow_left₀ (mul_nonneg hc (le_of_lt hεpos)) hce _
  have hnonneg : ∀ᶠ m : ℕ in Filter.atTop, (0 : ℝ) ≤ c ^ m * ‖a ^ m‖ :=
    Filter.Eventually.of_forall
      fun m => mul_nonneg (pow_nonneg hc _) (norm_nonneg _)
  have hlim : Filter.Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  exact squeeze_zero' hnonneg hbound hlim

end FunctionalAnalysis.LomonosovInvariantSubspaceWanted
