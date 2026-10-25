/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Def.Probability.LevyKhintchin.Part12
open MeasureTheory
open scoped ENNReal NNReal MeasureTheory Topology

/-!
# The Lévy–Khintchin representation

This file proves the one-dimensional Lévy–Khintchin characterization of infinitely divisible
probability measures, with the hard truncation convention at radius one.
-/


namespace MetaMathlibExt

lemma lk_canonicalMeasure_mass_le_bound {ρ : Measure ℝ} {L : ℝ → ℂ}
    (hprob : IsProbabilityMeasure ρ) (hL : Continuous L) (n : ℕ)
    (hρ : ∀ t, charFun ρ t = Complex.exp (L t / ((n + 1 : ℕ) : ℝ))) :
    (lkCanonicalMeasure ρ hprob n).mass ≤ lkCanonicalMassBound L := by
  apply NNReal.coe_le_coe.mp
  change ((lkCanonicalMeasure ρ hprob n).mass : ℝ) ≤
    16 * ∫ t : ℝ in (-1)..1, ‖L t‖ * Real.exp ‖L t‖
  exact lk_canonicalMeasure_mass_le hprob hL n hρ

lemma lk_canonicalMeasure_tail_le {ρ : Measure ℝ} {L : ℝ → ℂ}
    (hprob : IsProbabilityMeasure ρ) (hL : Continuous L) (n : ℕ)
    (hρ : ∀ t, charFun ρ t = Complex.exp (L t / ((n + 1 : ℕ) : ℝ)))
    {r : ℝ} (hr : 0 < r) :
    ((lkCanonicalMeasure ρ hprob n {x | r < |x|} : ℝ≥0) : ℝ) ≤
      (1 / 2 : ℝ) * r *
        ∫ t : ℝ in (-2 * r⁻¹)..(2 * r⁻¹), ‖L t‖ * Real.exp ‖L t‖ := by
  have htail := measureReal_abs_gt_le_integral_charFun (μ := ρ) hr
  have htail' : ρ.real {x | r < |x|} ≤ (1 / 2 : ℝ) * r *
      ‖∫ t : ℝ in (-2 * r⁻¹)..(2 * r⁻¹), 1 - charFun ρ t‖ := by
    norm_num at htail ⊢
    exact htail
  have hab : -2 * r⁻¹ ≤ 2 * r⁻¹ := by
    have := inv_pos.mpr hr
    linarith
  have hnorm := lk_norm_integral_scaled_one_sub_charFun_le hL n hρ
    (-2 * r⁻¹) (2 * r⁻¹) hab
  have hscale :
      ‖∫ t : ℝ in (-2 * r⁻¹)..(2 * r⁻¹),
        ((n + 1 : ℕ) : ℂ) * (1 - charFun ρ t)‖ =
      (n + 1 : ℝ) * ‖∫ t : ℝ in (-2 * r⁻¹)..(2 * r⁻¹), 1 - charFun ρ t‖ := by
    rw [intervalIntegral.integral_const_mul, Complex.norm_mul, Complex.norm_natCast]
    push_cast
    rfl
  rw [hscale] at hnorm
  calc
    ((lkCanonicalMeasure ρ hprob n {x | r < |x|} : ℝ≥0) : ℝ) ≤
        (n + 1 : ℝ) * ρ.real {x | r < |x|} :=
      lk_canonicalMeasure_apply_le ρ hprob n _
    _ ≤ (n + 1 : ℝ) * ((1 / 2 : ℝ) * r *
        ‖∫ t : ℝ in (-2 * r⁻¹)..(2 * r⁻¹), 1 - charFun ρ t‖) := by gcongr
    _ = (1 / 2 : ℝ) * r * ((n + 1 : ℝ) *
        ‖∫ t : ℝ in (-2 * r⁻¹)..(2 * r⁻¹), 1 - charFun ρ t‖) := by ring
    _ ≤ (1 / 2 : ℝ) * r *
        ∫ t : ℝ in (-2 * r⁻¹)..(2 * r⁻¹), ‖L t‖ * Real.exp ‖L t‖ := by gcongr

lemma lk_canonicalMeasure_tight_bound {ρ : ℕ → Measure ℝ} {L : ℝ → ℂ}
    (hprob : ∀ n, IsProbabilityMeasure (ρ n)) (hL : Continuous L) (hL0 : L 0 = 0)
    (hρ : ∀ n t, charFun (ρ n) t = Complex.exp (L t / ((n + 1 : ℕ) : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ n,
      ((lkCanonicalMeasure (ρ n) (hprob n) n {x | r < |x|} : ℝ≥0) : ℝ) ≤ ε := by
  let g : ℝ → ℝ := fun t ↦ ‖L t‖ * Real.exp ‖L t‖
  have hg : Continuous g := by
    dsimp only [g]
    fun_prop
  have hg0 : g 0 = 0 := by simp [g, hL0]
  obtain ⟨δ, hδ, hclose⟩ :=
    (Metric.continuousAt_iff.mp (hg.continuousAt : ContinuousAt g 0))
      (ε / 2) (by positivity)
  let r : ℝ := 4 / δ
  have hr : 0 < r := by dsimp [r]; positivity
  have hradius : 2 * r⁻¹ = δ / 2 := by
    dsimp [r]
    field_simp
    norm_num
  refine ⟨r, hr, fun n ↦ ?_⟩
  have hab : -2 * r⁻¹ ≤ 2 * r⁻¹ := by
    have := inv_pos.mpr hr
    linarith
  have hg_bound : ∀ t ∈ Set.Icc (-2 * r⁻¹) (2 * r⁻¹), g t ≤ ε / 2 := by
    intro t ht
    apply le_of_lt
    have htδ : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero]
      change (-2 * r⁻¹ ≤ t ∧ t ≤ 2 * r⁻¹) at ht
      have habst : |t| ≤ 2 * r⁻¹ := (abs_le).2 ⟨by linarith [ht.1], ht.2⟩
      rw [hradius] at habst
      nlinarith [abs_nonneg t]
    simpa [hg0, Real.dist_eq, abs_of_nonneg (by positivity : 0 ≤ g t)] using hclose htδ
  have hint : (∫ t : ℝ in (-2 * r⁻¹)..(2 * r⁻¹), g t) ≤
      ∫ _ : ℝ in (-2 * r⁻¹)..(2 * r⁻¹), ε / 2 :=
    intervalIntegral.integral_mono_on hab (hg.intervalIntegrable _ _)
      intervalIntegrable_const hg_bound
  rw [intervalIntegral.integral_const] at hint
  have htail := lk_canonicalMeasure_tail_le (hprob n) hL n (hρ n) hr
  change ((lkCanonicalMeasure (ρ n) (hprob n) n {x | r < |x|} : ℝ≥0) : ℝ) ≤ ε
  change _ ≤ (1 / 2 : ℝ) * r * (∫ t : ℝ in (-2 * r⁻¹)..(2 * r⁻¹), g t) at htail
  have hlen : 2 * r⁻¹ - -2 * r⁻¹ = 4 / r := by field_simp; ring
  rw [hlen, smul_eq_mul] at hint
  calc
    ((lkCanonicalMeasure (ρ n) (hprob n) n {x | r < |x|} : ℝ≥0) : ℝ) ≤
        (1 / 2 : ℝ) * r * (∫ t : ℝ in (-2 * r⁻¹)..(2 * r⁻¹), g t) := htail
    _ ≤ (1 / 2 : ℝ) * r * (4 / r * (ε / 2)) := by gcongr
    _ = ε := by field_simp; ring

lemma lk_exists_canonical_limit {ρ : ℕ → Measure ℝ} {L : ℝ → ℂ}
    (hprob : ∀ n, IsProbabilityMeasure (ρ n)) (hL : Continuous L) (hL0 : L 0 = 0)
    (hρ : ∀ n t, charFun (ρ n) t = Complex.exp (L t / ((n + 1 : ℕ) : ℝ))) :
    ∃ K : FiniteMeasure ℝ, ∃ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ Filter.atTop ∧
      Filter.Tendsto
        (fun n ↦ lkCanonicalMeasure (ρ n) (hprob n) n) U (𝓝 K) := by
  let u : ℕ → ℝ≥0 := fun m ↦ 1 / ((m : ℝ≥0) + 1)
  have hu : Filter.Tendsto u Filter.atTop (𝓝 0) := by
    simpa only [u] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
  have hex (m : ℕ) : ∃ r > 0, ∀ n,
      ((lkCanonicalMeasure (ρ n) (hprob n) n {x | r < |x|} : ℝ≥0) : ℝ) ≤
        (u m : ℝ) := by
    apply lk_canonicalMeasure_tight_bound hprob hL hL0 hρ
    dsimp only [u]
    positivity
  let r : ℕ → ℝ := fun m ↦ Classical.choose (hex m)
  have hr (m : ℕ) : 0 < r m := (Classical.choose_spec (hex m)).1
  have htail (m n : ℕ) :
      ((lkCanonicalMeasure (ρ n) (hprob n) n {x | r m < |x|} : ℝ≥0) : ℝ) ≤
        (u m : ℝ) :=
    (Classical.choose_spec (hex m)).2 n
  let C : ℝ≥0 := lkCanonicalMassBound L
  let A : ℕ → Set ℝ := fun m ↦ Set.Icc (-(r m)) (r m)
  have hA (m : ℕ) : IsCompact (A m) := isCompact_Icc
  let Kseq : ℕ → FiniteMeasure ℝ := fun n ↦
    lkCanonicalMeasure (ρ n) (hprob n) n
  have hmem (n : ℕ) : Kseq n ∈
      {K : FiniteMeasure ℝ | K.mass ≤ C ∧ ∀ m, K (A m)ᶜ ≤ u m} := by
    constructor
    · exact lk_canonicalMeasure_mass_le_bound (hprob n) hL n (hρ n)
    · intro m
      have hset : (A m)ᶜ = {x : ℝ | r m < |x|} := by
        ext x
        simp only [A, Set.mem_compl_iff, Set.mem_Icc, not_and_or, Set.mem_ofPred_eq]
        rw [lt_abs]
        grind
      rw [hset]
      apply NNReal.coe_le_coe.mp
      change ((lkCanonicalMeasure (ρ n) (hprob n) n {x | r m < |x|} : ℝ≥0) : ℝ) ≤
        (u m : ℝ)
      exact htail m n
  have hcompact := isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le
    C hu hA (Or.inl (inferInstance : NormalSpace ℝ))
  obtain ⟨K, -, hcluster⟩ := hcompact.exists_mapClusterPt
    (f := Filter.atTop) (u := Kseq)
    (Filter.tendsto_principal.mpr (Filter.Eventually.of_forall hmem))
  obtain ⟨U, hU, hconv⟩ := mapClusterPt_iff_ultrafilter.mp hcluster
  refine ⟨K, U, hU, ?_⟩
  simpa only [Kseq] using hconv

end MetaMathlibExt
