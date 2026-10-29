import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.DifferentialAnalysis.code.SimpleApproximation
open MeasureTheory Filter Set Finset
open scoped ENNReal NNReal


namespace SimpleApproximation

/--
[eapprox_ge_ennrealRatEmbed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SimpleApproximationFix.lean)
-/
@[path]
lemma eapprox_ge_ennrealRatEmbed
  [MeasurableSpace X]
  {f : X → ENNReal}
  {k n : ℕ}
  {x : X}
-- given
  (hf : Measurable f)
  (hk : k < n)
  (h : SimpleFunc.ennrealRatEmbed k ≤ f x) :
-- imply
  SimpleFunc.ennrealRatEmbed k ≤ SimpleFunc.eapprox f n x := by
-- proof
  simp only [SimpleFunc.eapprox, SimpleFunc.approx_apply x hf]
  exact Finset.le_sup_of_le (Finset.mem_range.mpr hk) (if_pos h ▸ le_refl _)

end SimpleApproximation

namespace SimpleApproximation

/--
[eapprox_ge_of_rational](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SimpleApproximationFix.lean)
-/
@[path]
lemma eapprox_ge_of_rational
  [MeasurableSpace X]
  {f : X → ENNReal}
  {q : ℚ}
  {x : X}
  {n : ℕ}
-- given
  (hf : Measurable f)
  (hqf : (ENNReal.ofNNReal (Real.toNNReal q)) ≤ f x)
  (hn : Encodable.encode q < n) :
-- imply
  (ENNReal.ofNNReal (Real.toNNReal q)) ≤ SimpleFunc.eapprox f n x := by
-- proof
  have h1 : SimpleFunc.ennrealRatEmbed (Encodable.encode q) ≤ f x := by
    rwa [SimpleFunc.ennrealRatEmbed_encode]
  have h2 := eapprox_ge_ennrealRatEmbed hf hn x h1
  rwa [SimpleFunc.ennrealRatEmbed_encode] at h2

end SimpleApproximation

namespace SimpleApproximation

/--
[toNNReal_nat_div](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SimpleApproximationFix.lean)
-/
@[path]
lemma toNNReal_nat_div
  [MeasurableSpace X]
  {k d : ℕ} :
-- imply
  Real.toNNReal ((k : ℚ) / (d : ℚ) : ℚ) = (k : NNReal) / (d : NNReal) := by
-- proof
  simp only [Rat.cast_div, Rat.cast_natCast]
  rw [Real.toNNReal_div (Nat.cast_nonneg k)]
  simp [Real.toNNReal_coe_nat]

end SimpleApproximation

namespace SimpleApproximation

/--
[eapprox_uniform_on_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SimpleApproximationFix.lean)
-/
@[path]
lemma eapprox_uniform_on_bounded
  [MeasurableSpace X]
  {f : X → ENNReal}
  {ε : ENNReal}
-- given
  (hf : Measurable f)
  (M : NNReal)
  (hε : 0 < ε) :
-- imply
  ∃ N : ℕ, ∀ n, N ≤ n → ∀ x, f x ≤ ↑M → f x - SimpleFunc.eapprox f n x ≤ ε := by
-- proof
  by_cases hε_top : ε = ⊤
  · exact ⟨0, fun n _ x _ => by simp [hε_top]⟩
  set ε' := ε.toNNReal with hε'_def
  have hε'_pos : 0 < ε' := ENNReal.toNNReal_pos (ne_of_gt hε) hε_top
  have hε_eq : ε = ↑ε' := (ENNReal.coe_toNNReal hε_top).symm
  obtain ⟨d, hd⟩ := exists_nat_gt (ε'⁻¹ : NNReal)
  have hd_pos : 0 < d := by
    by_contra h
    simp only [not_lt, Nat.le_zero] at h
    subst h; simp at hd
  have hd_inv : (d : NNReal)⁻¹ ≤ ε' :=
    (inv_le_comm₀ (Nat.cast_pos.mpr hd_pos) hε'_pos).mpr (le_of_lt hd)
  set K := Nat.ceil (M * d : NNReal) with hK_def
  set N := 1 + (Finset.range (K + 1)).sup
    (fun k => Encodable.encode ((k : ℚ) / (d : ℚ))) with hN_def
  refine ⟨N, fun n hn x hfx => ?_⟩
  have hfx_ne_top : f x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hfx
  set v := (f x).toNNReal with hv_def
  have hv_eq : f x = ↑v := (ENNReal.coe_toNNReal hfx_ne_top).symm
  have hv_le : v ≤ M := by
    rwa [← ENNReal.coe_le_coe, ← hv_eq]
  set k₀ := Nat.floor (v * d : NNReal) with hk₀_def
  set q₀ : ℚ := (k₀ : ℚ) / (d : ℚ) with hq₀_def
  have hq₀_nonneg : (0 : ℚ) ≤ q₀ := by positivity
  have hq₀_nnreal : Real.toNNReal q₀ = (k₀ : NNReal) / (d : NNReal) :=
    toNNReal_nat_div k₀ d
  have hk₀d_le_v : (k₀ : NNReal) / (d : NNReal) ≤ v := by
    rw [div_le_iff₀ (Nat.cast_pos.mpr hd_pos)]
    exact_mod_cast Nat.floor_le (v * d).2
  have herr : v - (k₀ : NNReal) / (d : NNReal) ≤ ε' := by
    calc v - (k₀ : NNReal) / (d : NNReal)
      ≤ (d : NNReal)⁻¹ := by
        rw [tsub_le_iff_right, inv_eq_one_div, ← add_div,
          le_div_iff₀ (Nat.cast_pos.mpr hd_pos), add_comm]
        exact le_of_lt (mod_cast Nat.lt_floor_add_one (v * d : NNReal))
      _ ≤ ε' := hd_inv
  have hk₀_le_K : k₀ ≤ K := by
    exact le_trans (Nat.floor_le_ceil _)
      (Nat.ceil_le_ceil (mul_le_mul_left hv_le d))
  have henc : Encodable.encode q₀ < N := by
    rw [hN_def]
    have hk₀_mem : k₀ ∈ Finset.range (K + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hk₀_le_K)
    have hsup : Encodable.encode q₀ ≤ (Finset.range (K + 1)).sup
      (fun k => Encodable.encode ((k : ℚ) / (d : ℚ))) := by
      rw [hq₀_def]
      exact @Finset.le_sup ℕ ℕ _ _ (Finset.range (K + 1))
        (fun k => Encodable.encode ((↑k : ℚ) / (↑d : ℚ))) k₀ hk₀_mem
    omega
  have henc_n : Encodable.encode q₀ < n := lt_of_lt_of_le henc hn
  have hq₀_le_fx : (ENNReal.ofNNReal (Real.toNNReal q₀)) ≤ f x := by
    rw [hq₀_nnreal, hv_eq]
    exact ENNReal.coe_le_coe.mpr hk₀d_le_v
  have heapprox_ge : (↑((k₀ : NNReal) / (d : NNReal)) : ENNReal) ≤ SimpleFunc.eapprox f n x := by
    have := eapprox_ge_of_rational hf q₀ x hq₀_le_fx henc_n
    rwa [hq₀_nnreal] at this
  calc f x - SimpleFunc.eapprox f n x
    ≤ f x - ↑((k₀ : NNReal) / (d : NNReal)) := tsub_le_tsub_left heapprox_ge _
    _ = ↑v - ↑((k₀ : NNReal) / (d : NNReal)) := by rw [hv_eq]
    _ = ↑(v - (k₀ : NNReal) / (d : NNReal)) := (ENNReal.coe_sub).symm
    _ ≤ ↑ε' := ENNReal.coe_le_coe.mpr herr
    _ = ε := hε_eq.symm

end SimpleApproximation

namespace SimpleApproximation

/--
[exists_monotone_simple_approx_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SimpleApproximationFix.lean)
-/
@[path]
lemma exists_monotone_simple_approx_uniform
  [MeasurableSpace X]
  {f : X → ENNReal}
-- given
  (hf : Measurable f) :
-- imply
  ∃ (g : ℕ → X → ENNReal), (∀ n, Measurable (g n)) ∧ (∀ n, (Set.range (g n)).Finite) ∧ (∀ n x, g n x ≤ g (n + 1) x) ∧ (∀ x, Filter.Tendsto (fun n => g n x) Filter.atTop (nhds (f x))) ∧ (∀ (M : NNReal) {ε : ENNReal}, 0 < ε → ∃ N, ∀ n, N ≤ n → ∀ x, f x ≤ ↑M → f x - g n x ≤ ε) := by
-- proof
  refine ⟨fun n => (↑(SimpleFunc.eapprox f n) : X → ENNReal), ?_, ?_, ?_, ?_, ?_⟩
  · intro n; exact (SimpleFunc.eapprox f n).measurable
  · intro n; exact (SimpleFunc.eapprox f n).finite_range
  · intro n x; exact SimpleFunc.monotone_eapprox f (Nat.le_succ n) x
  · intro x; exact SimpleFunc.tendsto_eapprox hf x
  · intro M ε hε; exact eapprox_uniform_on_bounded hf M hε

end SimpleApproximation


-- created on 2026-10-23
