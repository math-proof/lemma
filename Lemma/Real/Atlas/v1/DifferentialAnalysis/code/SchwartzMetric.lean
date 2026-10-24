import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.SchwartzMetric
open Filter TemperedDistributions
open scoped SchwartzMap


namespace TemperedDistributions

/--
[supSeminorm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzMetric.lean)
-/
@[path]
lemma supSeminorm_nonneg
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  {k : ℕ}
  {f : 𝓢(E, F)} :
-- imply
  0 ≤ supSeminorm k f :=
-- proof
  apply_nonneg (supSeminorm k) f

end TemperedDistributions

namespace TemperedDistributions

/--
[individual_le_supSeminorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzMetric.lean)
-/
@[path]
lemma individual_le_supSeminorm
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  {k n K : ℕ}
  {f : 𝓢(E, F)}
-- given
  (hk : k ≤ K)
  (hn : n ≤ K) :
-- imply
  SchwartzMap.seminorm ℝ k n f ≤ supSeminorm K f :=
-- proof
  SchwartzSeminorms.individual_le_sup_seminorm hk hn f

end TemperedDistributions

namespace TemperedDistributions

/--
[boundedSeminormTerm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzMetric.lean)
-/
@[path]
lemma boundedSeminormTerm_nonneg
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  {k : ℕ}
  {u v : 𝓢(E, F)} :
-- imply
  0 ≤ boundedSeminormTerm k u v := by
-- proof
  unfold boundedSeminormTerm
  apply mul_nonneg
  · positivity
  · exact div_nonneg (supSeminorm_nonneg k (u - v))
    (by linarith [supSeminorm_nonneg k (u - v)])

end TemperedDistributions

namespace TemperedDistributions

/--
[boundedSeminormTerm_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzMetric.lean)
-/
@[path]
lemma boundedSeminormTerm_le
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  {k : ℕ}
  {u v : 𝓢(E, F)} :
-- imply
  boundedSeminormTerm k u v ≤ ((1 : ℝ) / 2) ^ k := by
-- proof
  unfold boundedSeminormTerm
  have hs := supSeminorm_nonneg k (u - v)
  have hfrac : supSeminorm k (u - v) /
    (1 + supSeminorm k (u - v)) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  calc ((1 : ℝ) / 2) ^ k * (supSeminorm k (u - v) /
    (1 + supSeminorm k (u - v)))
    ≤ ((1 : ℝ) / 2) ^ k * 1 := by
      apply mul_le_mul_of_nonneg_left hfrac; positivity
    _ = ((1 : ℝ) / 2) ^ k := mul_one _

end TemperedDistributions

namespace TemperedDistributions

/--
[summable_boundedSeminormTerm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzMetric.lean)
-/
@[path]
lemma summable_boundedSeminormTerm
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  {u v : 𝓢(E, F)} :
-- imply
  Summable (fun k => boundedSeminormTerm k u v) :=
-- proof
  Summable.of_nonneg_of_le (boundedSeminormTerm_nonneg · u v)
    (boundedSeminormTerm_le · u v) summable_geometric_two

end TemperedDistributions

namespace TemperedDistributions

/--
[div_one_add_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzMetric.lean)
-/
@[path]
lemma div_one_add_triangle
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  {a b c : ℝ}
-- given
  (ha : 0 ≤ a)
  (hb : 0 ≤ b)
  (hc : 0 ≤ c)
  (h : c ≤ a + b) :
-- imply
  c / (1 + c) ≤ a / (1 + a) + b / (1 + b) := by
-- proof
  have h1a : 0 < 1 + a := by linarith
  have h1b : 0 < 1 + b := by linarith
  have h1c : 0 < 1 + c := by linarith
  rw [div_add_div _ _ (ne_of_gt h1a) (ne_of_gt h1b),
    div_le_div_iff₀ h1c (mul_pos h1a h1b)]
  nlinarith [mul_nonneg ha hb]

end TemperedDistributions

namespace TemperedDistributions

/--
[boundedSeminormTerm_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzMetric.lean)
-/
@[path]
lemma boundedSeminormTerm_triangle
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  {k : ℕ}
  {u v w : 𝓢(E, F)} :
-- imply
  boundedSeminormTerm k u w ≤ boundedSeminormTerm k u v + boundedSeminormTerm k v w := by
-- proof
  unfold boundedSeminormTerm
  have ha := supSeminorm_nonneg k (u - v)
  have hb := supSeminorm_nonneg k (v - w)
  have hc := supSeminorm_nonneg k (u - w)
  have hsub : u - w = (u - v) + (v - w) := by abel
  have htri : supSeminorm k (u - w) ≤
    supSeminorm k (u - v) + supSeminorm k (v - w) := by
    rw [hsub]
    exact map_add_le_add _ _ _
  have hkey := div_one_add_triangle ha hb hc htri
  calc ((1 : ℝ) / 2) ^ k * (supSeminorm k (u - w) /
    (1 + supSeminorm k (u - w)))
    ≤ ((1 : ℝ) / 2) ^ k * (supSeminorm k (u - v) /
      (1 + supSeminorm k (u - v)) +
      supSeminorm k (v - w) /
      (1 + supSeminorm k (v - w))) := by
      apply mul_le_mul_of_nonneg_left hkey; positivity
    _ = ((1 : ℝ) / 2) ^ k * (supSeminorm k (u - v) /
      (1 + supSeminorm k (u - v))) +
      ((1 : ℝ) / 2) ^ k * (supSeminorm k (v - w) /
      (1 + supSeminorm k (v - w))) := by ring

end TemperedDistributions

namespace TemperedDistributions

/--
[boundedSeminormTerm_le_schwartzDist](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzMetric.lean)
-/
@[path]
lemma boundedSeminormTerm_le_schwartzDist
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  {k : ℕ}
  {u v : 𝓢(E, F)} :
-- imply
  boundedSeminormTerm k u v ≤ schwartzDist u v := by
-- proof
  unfold schwartzDist
  have := (summable_boundedSeminormTerm u v).sum_le_tsum {k}
    (fun i _ => boundedSeminormTerm_nonneg i u v)
  simpa using this

end TemperedDistributions

namespace TemperedDistributions

/--
[schwartzDist_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzMetric.lean)
-/
@[path]
lemma schwartzDist_nonneg
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  {u v : 𝓢(E, F)} :
-- imply
  0 ≤ schwartzDist u v := by
-- proof
  unfold schwartzDist
  exact tsum_nonneg (fun k => boundedSeminormTerm_nonneg k u v)

end TemperedDistributions

namespace TemperedDistributions

/--
[schwartzDist_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzMetric.lean)
-/
@[path]
lemma schwartzDist_self
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  {u : 𝓢(E, F)} :
-- imply
  schwartzDist u u = 0 := by
-- proof
  unfold schwartzDist boundedSeminormTerm
  simp [sub_self, map_zero]

end TemperedDistributions

namespace TemperedDistributions

/--
[schwartzDist_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzMetric.lean)
-/
@[path]
lemma schwartzDist_comm
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  {u v : 𝓢(E, F)} :
-- imply
  schwartzDist u v = schwartzDist v u := by
-- proof
  unfold schwartzDist boundedSeminormTerm
  congr 1
  ext k
  rw [map_sub_rev (supSeminorm k)]

end TemperedDistributions

namespace TemperedDistributions

/--
[schwartzDist_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzMetric.lean)
-/
@[path]
lemma schwartzDist_triangle
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  {u v w : 𝓢(E, F)} :
-- imply
  schwartzDist u w ≤ schwartzDist u v + schwartzDist v w := by
-- proof
  unfold schwartzDist
  calc ∑' k, boundedSeminormTerm k u w
    ≤ ∑' k, (boundedSeminormTerm k u v + boundedSeminormTerm k v w) := by
      apply Summable.tsum_mono (summable_boundedSeminormTerm u w)
      · exact (summable_boundedSeminormTerm u v).add (summable_boundedSeminormTerm v w)
      · intro k
        exact boundedSeminormTerm_triangle k u v w
    _ = ∑' k, boundedSeminormTerm k u v + ∑' k, boundedSeminormTerm k v w :=
      Summable.tsum_add (summable_boundedSeminormTerm u v) (summable_boundedSeminormTerm v w)

end TemperedDistributions

namespace TemperedDistributions

/--
[schwartzDist_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzMetric.lean)
-/
@[path]
lemma schwartzDist_eq_zero_iff
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  {u v : 𝓢(E, F)} :
-- imply
  schwartzDist u v = 0 ↔ u = v := by
-- proof
  constructor
  · intro h
    have hterms : ∀ k, boundedSeminormTerm k u v = 0 := by
      intro k
      have h1 := boundedSeminormTerm_nonneg k u v
      have h2 := boundedSeminormTerm_le_schwartzDist k u v
      linarith
    have hsup0 : supSeminorm 0 (u - v) = 0 := by
      have h0 := hterms 0
      unfold boundedSeminormTerm at h0
      simp at h0
      have hs := supSeminorm_nonneg 0 (u - v)
      cases h0 with
      | inl h => exact h
      | inr h => linarith
    have h00 : SchwartzMap.seminorm ℝ 0 0 (u - v) = 0 := by
      have hle := individual_le_supSeminorm (le_refl 0) (le_refl 0) (u - v)
      linarith [apply_nonneg (SchwartzMap.seminorm ℝ 0 0) (u - v)]
    exact sub_eq_zero.mp <| by
      ext x
      have hle := SchwartzMap.le_seminorm ℝ 0 0 (u - v) x
      simp [h00] at hle
      exact hle
  · intro h
    subst h
    exact schwartzDist_self u

end TemperedDistributions

namespace TemperedDistributions

/--
[norm_boundedSeminormTerm_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzMetric.lean)
-/
@[path]
lemma norm_boundedSeminormTerm_le
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  {k : ℕ}
  {u v : 𝓢(E, F)} :
-- imply
  ‖boundedSeminormTerm k u v‖ ≤ ((1 : ℝ) / 2) ^ k := by
-- proof
  rw [Real.norm_of_nonneg (boundedSeminormTerm_nonneg k u v)]
  exact boundedSeminormTerm_le k u v

end TemperedDistributions

namespace TemperedDistributions

/--
[frac_tendsto_zero_of_nonneg_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzMetric.lean)
-/
@[path]
lemma frac_tendsto_zero_of_nonneg_tendsto_zero
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  {s : ℕ → ℝ}
-- given
  (hs : ∀ n, 0 ≤ s n)
  (h : Tendsto s atTop (nhds 0)) :
-- imply
  Tendsto (fun n => s n / (1 + s n)) atTop (nhds 0) :=
-- proof
  squeeze_zero_norm' (f := fun n => s n / (1 + s n)) (a := s)
    (.of_forall fun n => by
      rw [Real.norm_of_nonneg (div_nonneg (hs n) (by linarith [hs n]))]
      exact div_le_self (hs n) (by linarith [hs n])) h

end TemperedDistributions

namespace TemperedDistributions

/--
[boundedSeminormTerm_tendsto_of_supSeminorm_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzMetric.lean)
-/
@[path]
lemma boundedSeminormTerm_tendsto_of_supSeminorm_tendsto
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  {k : ℕ}
  {u : ℕ → 𝓢(E, F)}
  {v : 𝓢(E, F)}
-- given
  (h : Tendsto (fun n => supSeminorm k (u n - v)) atTop (nhds 0)) :
-- imply
  Tendsto (fun n => boundedSeminormTerm k (u n) v) atTop (nhds 0) := by
-- proof
  simp only [boundedSeminormTerm]
  have h1 := frac_tendsto_zero_of_nonneg_tendsto_zero _
    (fun n => supSeminorm_nonneg k (u n - v)) h
  have h2 := h1.const_mul (((1 : ℝ) / 2) ^ k)
  simp only [mul_zero] at h2; exact h2

end TemperedDistributions

namespace TemperedDistributions

/--
[schwartzDist_cauchy_implies_seminorm_cauchy](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzMetric.lean)
-/
@[path]
lemma schwartzDist_cauchy_implies_seminorm_cauchy
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  {u : ℕ → 𝓢(E, F)}
  {k : ℕ}
-- given
  (hcauchy : ∀ ε > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m → schwartzDist (u n) (u m) < ε) :
-- imply
  ∀ ε > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m → supSeminorm k (u n - u m) < ε := by
-- proof
  intro ε hε
  set δ := ε / (1 + ε)
  have hδ_pos : 0 < δ := div_pos hε (by linarith)
  have hδ_lt : δ < 1 := by
    show ε / (1 + ε) < 1; rw [div_lt_one (by linarith : 0 < 1 + ε)]; linarith
  have hpow : (0 : ℝ) < ((1 : ℝ) / 2) ^ k := by positivity
  obtain ⟨N, hN⟩ := hcauchy (δ * ((1 : ℝ) / 2) ^ k) (mul_pos hδ_pos hpow)
  refine ⟨N, fun n m hn hm => ?_⟩
  set s := supSeminorm k (u n - u m)
  have hs : 0 ≤ s := supSeminorm_nonneg k (u n - u m)
  have h1s : 0 < 1 + s := by linarith
  have h1δ : 0 < 1 - δ := by linarith
  have h_frac : s / (1 + s) < δ := by
    have h1 : ((1 : ℝ) / 2) ^ k * (s / (1 + s)) < ((1 : ℝ) / 2) ^ k * δ := by
      calc _ ≤ schwartzDist (u n) (u m) := boundedSeminormTerm_le_schwartzDist k (u n) (u m)
        _ < δ * ((1 : ℝ) / 2) ^ k := hN n m hn hm
        _ = ((1 : ℝ) / 2) ^ k * δ := by ring
    exact lt_of_mul_lt_mul_left h1 hpow.le
  have hlt : s < δ / (1 - δ) := by
    rw [lt_div_iff₀ h1δ]; rw [div_lt_iff₀ h1s] at h_frac; nlinarith
  have h1ε : (1 : ℝ) + ε ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 1 + ε)
  have hδ_eq : δ / (1 - δ) = ε := by
    show ε / (1 + ε) / (1 - ε / (1 + ε)) = ε
    have key : 1 - ε / (1 + ε) = 1 / (1 + ε) := by field_simp; ring
    rw [key, div_div_eq_mul_div, mul_comm, mul_div_assoc']; simp [h1ε]
  linarith

end TemperedDistributions

namespace TemperedDistributions

/--
[schwartz_seminorm_cauchy_converges](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzMetric.lean)
-/
@[path]
lemma schwartz_seminorm_cauchy_converges
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  {u : ℕ → 𝓢(E, F)}
-- given
  (hcauchy : ∀ K : ℕ, ∀ ε > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m → (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (u n - u m) < ε) :
-- imply
  ∃ v : 𝓢(E, F), ∀ K : ℕ, Tendsto (fun n => (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (u n - v)) atTop (nhds 0) := by
-- proof
  haveI : CompleteSpace 𝓢(E, F) := instCompleteSpaceSchwartz
  have hcs : CauchySeq u := diag_cauchy_implies_cauchySeq u hcauchy
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨v, fun K => ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hws := schwartz_withSeminorms ℝ E F
  have h_ind : ∀ p ∈ Finset.Iic (K, K),
    ∃ N, ∀ n, N ≤ n → SchwartzMap.seminorm ℝ p.1 p.2 (u n - v) < ε := by
    intro ⟨j, l⟩ _
    have hcont := hws.continuous_seminorm (j, l)
    have hsub : Tendsto (fun n => u n - v) atTop (nhds 0) := by
      rw [show (0 : 𝓢(E, F)) = v - v from (sub_self v).symm]
      exact hv.sub tendsto_const_nhds
    have htend := (hcont.tendsto 0).comp hsub
    simp only [map_zero, Function.comp_def] at htend
    rw [Metric.tendsto_atTop] at htend
    obtain ⟨N, hN⟩ := htend ε hε
    exact ⟨N, fun n hn => by
      have := hN n hn
      rwa [dist_zero_right, Real.norm_of_nonneg (apply_nonneg _ _)] at this⟩
  classical
  choose! Nf hNf using h_ind
  refine ⟨(Finset.Iic (K, K)).sup Nf, fun n hn => ?_⟩
  rw [dist_zero_right, Real.norm_of_nonneg (apply_nonneg _ _)]
  apply Seminorm.finset_sup_apply_lt hε
  intro m hm
  exact hNf m hm n (le_trans (Finset.le_sup hm) hn)

end TemperedDistributions

namespace TemperedDistributions

/--
[schwartzDist_tendsto_of_seminorm_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzMetric.lean)
-/
@[path]
lemma schwartzDist_tendsto_of_seminorm_tendsto
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  {u : ℕ → 𝓢(E, F)}
  {v : 𝓢(E, F)}
-- given
  (h : ∀ k, Tendsto (fun n => supSeminorm k (u n - v)) atTop (nhds 0)) :
-- imply
  Tendsto (fun n => schwartzDist (u n) v) atTop (nhds 0) := by
-- proof
  simp only [schwartzDist]
  have h_dom := @tendsto_tsum_of_dominated_convergence ℕ ℕ ℝ atTop _ _
    (fun n k => boundedSeminormTerm k (u n) v) (fun _ => 0)
    (fun k => ((1 : ℝ) / 2) ^ k) summable_geometric_two
    (fun k => boundedSeminormTerm_tendsto_of_supSeminorm_tendsto k u v (h k))
    (.of_forall fun n k => norm_boundedSeminormTerm_le k (u n) v)
  simp at h_dom; exact h_dom

end TemperedDistributions

namespace TemperedDistributions

/--
[schwartzDist_complete](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzMetric.lean)
-/
@[path]
lemma schwartzDist_complete
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F] :
-- imply
  ∀ u : ℕ → 𝓢(E, F), (∀ ε > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m → schwartzDist (u n) (u m) < ε) → ∃ v : 𝓢(E, F), Tendsto (fun n => schwartzDist (u n) v) atTop (nhds 0) := by
-- proof
  intro u hcauchy
  have h_sem_cauchy := schwartzDist_cauchy_implies_seminorm_cauchy u hcauchy
  obtain ⟨v, hv⟩ := schwartz_seminorm_cauchy_converges u h_sem_cauchy
  exact ⟨v, schwartzDist_tendsto_of_seminorm_tendsto u v hv⟩

end TemperedDistributions

namespace TemperedDistributions

/--
[schwartzDist_metric_axioms](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzMetric.lean)
-/
@[path]
lemma schwartzDist_metric_axioms
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  {u v w : 𝓢(E, F)} :
-- imply
  schwartzDist u u = 0 ∧ schwartzDist u v = schwartzDist v u ∧ schwartzDist u w ≤ schwartzDist u v + schwartzDist v w ∧ (schwartzDist u v = 0 ↔ u = v) ∧ (∀ (s : ℕ → 𝓢(E, F)), (∀ ε > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m → schwartzDist (s n) (s m) < ε) → ∃ a : 𝓢(E, F), Tendsto (fun n => schwartzDist (s n) a) atTop (nhds 0)) :=
-- proof
  ⟨schwartzDist_self u, schwartzDist_comm u v, schwartzDist_triangle u v w,
    schwartzDist_eq_zero_iff u v, schwartzDist_complete⟩

end TemperedDistributions


-- created on 2026-10-23
