import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter9.Martingales
open MeasureTheory Filter Set SimpleGraph ShamirSpencer Martingales
open MeasureTheory ProbabilityTheory Real
open scoped NNReal


namespace ShamirSpencer

/--
[colorable_of_induce_compl_colorable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/Martingales.lean)
-/
@[path]
lemma colorable_of_induce_compl_colorable
  {n : ℕ}
  {G : SimpleGraph (Fin n)}
  {u : ℕ}
  {S : Finset (Fin n)}
-- given
  (h0 : (G.induce (↑Sᶜ : Set (Fin n))).Colorable u)
  (h1 : (G.induce (↑S : Set (Fin n))).Colorable 3) :
-- imply
  G.Colorable (u + 3) := by
-- proof
  obtain ⟨c1⟩ := h1
  obtain ⟨c2⟩ := h2
  constructor
  refine ⟨fun v => ?_, ?_⟩
  · by_cases hv : (v : Fin n) ∈ S
    · exact ⟨u + (c2 ⟨v, hv⟩).val, by omega⟩
    · have hv' : v ∈ (↑Sᶜ : Set (Fin n)) := by simp [hv]
      exact ⟨(c1 ⟨v, hv'⟩).val, by omega⟩
  · intro v w hvw
    simp only
    by_cases hv : v ∈ S <;> by_cases hw : w ∈ S
    · simp [hv, hw]
      have hadj : (G.induce (↑S : Set (Fin n))).Adj ⟨v, hv⟩ ⟨w, hw⟩ := by
        rw [induce_adj]; exact hvw
      have := c2.valid hadj
      simp [Ne, Fin.ext_iff] at this
      omega
    · simp [hv, hw]
      omega
    · simp [hv, hw]
      omega
    · simp [hv, hw]
      have hv' : v ∈ (↑Sᶜ : Set (Fin n)) := by simp [hv]
      have hw' : w ∈ (↑Sᶜ : Set (Fin n)) := by simp [hw]
      have hadj : (G.induce (↑Sᶜ : Set (Fin n))).Adj ⟨v, hv'⟩ ⟨w, hw'⟩ := by
        rw [induce_adj]; exact hvw
      have := c1.valid hadj
      simp [Ne, Fin.ext_iff] at this
      omega

end ShamirSpencer

namespace ShamirSpencer

/--
[chromaticNumberNat_le_of_deletion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/Martingales.lean)
-/
@[path]
lemma chromaticNumberNat_le_of_deletion
  {n : ℕ}
  {G : SimpleGraph (Fin n)}
  {u : ℕ}
  {S : Finset (Fin n)}
-- given
  (h0 : (G.induce (↑Sᶜ : Set (Fin n))).Colorable u)
  (h1 : (G.induce (↑S : Set (Fin n))).Colorable 3) :
-- imply
  chromaticNumberNat n G ≤ u + 3 :=
-- proof
  ENat.toNat_le_of_le_coe (colorable_of_induce_compl_colorable G u S h1 h2).chromaticNumber_le

end ShamirSpencer

namespace ShamirSpencer

/--
[three_events_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/Martingales.lean)
-/
@[path]
lemma three_events_subset
  {n : ℕ}
  {u : ℕ}
  {C : ℝ} :
-- imply
  ({G : SimpleGraph (Fin n) | ∃ S : Finset (Fin n), (S.card : ℝ) ≤ C * Real.sqrt (↑n) ∧ (G.induce (↑Sᶜ : Set (Fin n))).Colorable u} ∩ {G | ∀ S : Finset (Fin n), (S.card : ℝ) ≤ C * Real.sqrt (↑n) → (G.induce (↑S : Set (Fin n))).Colorable 3} ∩ {G | u ≤ chromaticNumberNat n G}) ⊆ {G | u ≤ chromaticNumberNat n G ∧ chromaticNumberNat n G ≤ u + 3} := by
-- proof
  intro G hG
  obtain ⟨⟨hG1, hG2⟩, hG3⟩ := hG
  obtain ⟨S, hS_card, hS_col⟩ := hG1
  exact ⟨hG3, chromaticNumberNat_le_of_deletion G u S hS_col (hG2 S hS_card)⟩
/-- **Shamir–Spencer four-value concentration of the chromatic number.** For sparse Erdős–Rényi
graphs $G(n, p)$ with $p < n^{-\alpha}$ and $\alpha > 5/6$, there exists a sequence $u(n)$ such
that with probability at least $1 - 3\varepsilon$, $u(n) \le \chi(G) \le u(n) + 3$ for all
sufficiently large $n$. The proof combines the Azuma-type bounded-difference inequality with
a $3$-colourability property of small induced subgraphs. -/
end ShamirSpencer
namespace Martingales
open MeasureTheory ProbabilityTheory Real
open scoped NNReal


namespace Martingales

/--
[azuma_inequality_alt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/Martingales.lean)
-/
@[path]
lemma azuma_inequality_alt
  {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  [StandardBorelSpace Ω]
  {ℱ : MeasureTheory.Filtration ℕ mΩ}
  {Z : ℕ → Ω → ℝ}
  {n : ℕ}
  {c : Fin n → ℝ}
  {t : ℝ}
-- given
  (hmart : MeasureTheory.Martingale Z ℱ μ)
  (hc_pos : ∀ i, 0 ≤ c i)
  (hbdd : ∀ i : Fin n, ∀ᵐ ω ∂μ, |Z (↑i + 1) ω - Z ↑i ω| ≤ c i)
  (h_adapted : MeasureTheory.StronglyAdapted ℱ (fun i ω => Z (i + 1) ω - Z i ω))
  (σ : ℕ → ℝ≥0)
  (hσ : ∀ i (hi : i < n), (σ i : ℝ) = c ⟨i, hi⟩ ^ 2)
  (h0 : ProbabilityTheory.HasSubgaussianMGF (fun ω => Z 1 ω - Z 0 ω) (σ 0) μ)
  (h_subG : ∀ i, i < n - 1 → ProbabilityTheory.HasCondSubgaussianMGF (↑(ℱ i)) (ℱ.le i) (fun ω => Z (i + 2) ω - Z (i + 1) ω) (σ (i + 1)) μ)
  (ht : 0 < t) :
-- imply
  μ.real {ω | Z n ω - Z 0 ω ≥ t} ≤ Real.exp (-t ^ 2 / (2 * ∑ i : Fin n, c i ^ 2)) := by
-- proof
  set Y : ℕ → Ω → ℝ := fun i ω => Z (i + 1) ω - Z i ω
  have htelescope : ∀ ω, Z n ω - Z 0 ω = ∑ i ∈ Finset.range n, Y i ω :=
    fun ω => (Finset.sum_range_sub (fun i => Z i ω) n).symm
  have hset_eq : {ω | Z n ω - Z 0 ω ≥ t} =
    {ω | t ≤ ∑ i ∈ Finset.range n, Y i ω} := by
    ext ω; simp only [Set.mem_setOf_eq, ge_iff_le, htelescope ω]
  rw [hset_eq]
  have hε : (0 : ℝ) ≤ t := le_of_lt ht
  have hmain := ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF
    (cY := σ) h_adapted h0 n h_subG hε
  refine hmain.trans (Real.exp_le_exp.mpr ?_)
  suffices h : (↑(∑ i ∈ Finset.range n, σ i) : ℝ) = ∑ i : Fin n, c i ^ 2 by rw [h]
  rw [NNReal.coe_sum]
  have hfin : ∑ i : Fin n, c i ^ 2 = ∑ i ∈ Finset.range n,
    (if h : i < n then c ⟨i, h⟩ ^ 2 else 0) := Finset.sum_fin_eq_sum_range ..
  rw [hfin]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dif_pos (Finset.mem_range.mp hi)]
  exact hσ i (Finset.mem_range.mp hi)

end Martingales

namespace Martingales

/--
[hoeffding_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/Martingales.lean)
-/
@[path]
lemma hoeffding_lemma
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {X : Ω → ℝ}
  {a ℓ : ℝ}
  {t : ℝ}
-- given
  (hX : AEMeasurable X μ)
  (hE : ∫ ω, X ω ∂μ = 0)
  (hℓ : 0 ≤ ℓ)
  (hbnd : ∀ᵐ ω ∂μ, a ≤ X ω ∧ X ω ≤ a + ℓ) :
-- imply
  ∫ ω, Real.exp (t * X ω) ∂μ ≤ Real.exp (t ^ 2 * ℓ ^ 2 / 8) := by
-- proof
  have hIcc : ∀ᵐ ω ∂μ, X ω ∈ Icc a (a + ℓ) := by
    filter_upwards [hbnd] with ω ⟨h1, h2⟩; exact ⟨h1, h2⟩
  have hSubG := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hX hIcc hE
  have hmgf := hSubG.mgf_le t
  simp only [mgf] at hmgf
  refine hmgf.trans (Real.exp_le_exp.mpr ?_)
  have hab : (a + ℓ) - a = ℓ := by ring
  rw [hab]
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat]
  rw [Real.nnnorm_of_nonneg hℓ]
  push_cast
  linarith

end Martingales

namespace Martingales

/--
[azuma_doob_martingale_subG](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/Martingales.lean)
-/
@[path]
lemma azuma_doob_martingale_subG
  {mΩ : MeasurableSpace Ω}
  [StandardBorelSpace Ω]
  {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ]
  {ℱ : MeasureTheory.Filtration ℕ mΩ}
  {Y : ℕ → Ω → ℝ}
  {c : ℕ → ℝ}
  {n : ℕ}
  {ε : ℝ}
-- given
  (hc : ∀ i, 0 ≤ c i)
  (h_adapted : MeasureTheory.StronglyAdapted ℱ Y)
  (h0 : ProbabilityTheory.HasSubgaussianMGF (Y 0) (hoeffdingSubGParam (c 0) (hc 0)) μ)
  (h_subG : ∀ i, i < n - 1 → ProbabilityTheory.HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (hoeffdingSubGParam (c (i + 1)) (hc (i + 1))) μ)
  (hε : 0 ≤ ε) :
-- imply
  μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω} ≤ Real.exp (-2 * ε ^ 2 / ∑ i ∈ Finset.range n, c i ^ 2) := by
-- proof
  set cY : ℕ → ℝ≥0 := fun i => hoeffdingSubGParam (c i) (hc i) with hcY_def
  have hmain := ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF
    (ℱ := ℱ) (cY := cY) h_adapted h0 n h_subG hε
  refine hmain.trans (Real.exp_le_exp.mpr ?_)
  have hcY_eq : (↑(∑ i ∈ Finset.range n, cY i) : ℝ) = (∑ i ∈ Finset.range n, c i ^ 2) / 4 := by
    rw [NNReal.coe_sum]
    simp only [hcY_def, hoeffdingSubGParam, NNReal.coe_mk]
    rw [Finset.sum_div]
  rw [hcY_eq]
  by_cases hS : ∑ x ∈ Finset.range n, c x ^ 2 = 0
  · simp [hS]
  · rw [show (2 : ℝ) * ((∑ x ∈ Finset.range n, c x ^ 2) / 4) =
    (∑ x ∈ Finset.range n, c x ^ 2) / 2 by ring]
    rw [show -ε ^ 2 / ((∑ x ∈ Finset.range n, c x ^ 2) / 2) =
      -2 * ε ^ 2 / ∑ x ∈ Finset.range n, c x ^ 2 by field_simp]

end Martingales

namespace Martingales

/--
[hasSubgaussianMGF_of_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/Martingales.lean)
-/
@[path]
lemma hasSubgaussianMGF_of_bounded
  {mΩ : MeasurableSpace Ω}
  [StandardBorelSpace Ω]
  {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ]
  {X : Ω → ℝ}
  {c : ℝ}
-- given
  (hc : 0 ≤ c)
  (h_mean : ∫ ω, X ω ∂μ = 0)
  (h_meas : AEMeasurable X μ)
  (h_bnd : ∃ a₀ : ℝ, ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a₀ (a₀ + c)) :
-- imply
  HasSubgaussianMGF X (hoeffdingSubGParam c hc) μ := by
-- proof
  obtain ⟨a₀, ha₀⟩ := h_bnd
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero h_meas ha₀ h_mean
  rw [show a₀ + c - a₀ = c from by ring] at h
  have hparam : (‖c‖₊ / 2) ^ 2 = hoeffdingSubGParam c hc := by
    unfold hoeffdingSubGParam
    rw [Real.nnnorm_of_nonneg hc]
    ext
    push_cast
    ring
  rwa [hparam] at h
/-- Conditional version of `hasSubgaussianMGF_of_bounded`: a variable with vanishing conditional
mean given $m$ and contained in an interval $[a(\omega), a(\omega) + c]$ (with $a$ being
$m$-measurable) has a conditionally sub-Gaussian MGF with the Hoeffding parameter $c^{2}/4$. -/

end Martingales


-- created on 2026-10-23
