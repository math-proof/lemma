import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.GraphContainers
open SimpleGraph Finset GraphContainers
open scoped Classical


namespace GraphContainers

/--
[badEvent_subset_container_union](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/GraphContainers.lean)
-/
@[path]
lemma badEvent_subset_container_union
  {n : ℕ}
  {ε : ℝ}
  {𝒞 : Finset (SimpleGraph (Fin n))}
  {p : ℝ}
-- given
  (hcover : ∀ H : SimpleGraph (Fin n), H.CliqueFree 3 → ∃ G ∈ 𝒞, H ≤ G) :
-- imply
  badEvent n ((1/4 + 2*ε) * p * (n : ℝ)^2) ⊆ ⋃ C ∈ 𝒞, {G : SimpleGraph (Fin n) | ((C ⊓ G).edgeFinset.card : ℝ) > (1/4 + 2*ε) * p * (n : ℝ)^2} := by
-- proof
  intro G hG
  simp only [badEvent, Set.mem_setOf_eq] at hG
  obtain ⟨H, hHG, hHfree, hHedges⟩ := hG
  obtain ⟨C, hCmem, hHC⟩ := hcover H hHfree
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  refine ⟨C, hCmem, ?_⟩
  have hH_inf : H ≤ C ⊓ G := le_inf hHC hHG
  have hcard : H.edgeFinset.card ≤ (C ⊓ G).edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hH_inf)
  linarith [show (H.edgeFinset.card : ℝ) ≤ ((C ⊓ G).edgeFinset.card : ℝ) from by
    exact_mod_cast hcard]

end GraphContainers

namespace GraphContainers

/--
[asymptotic_bound_pointwise](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/GraphContainers.lean)
-/
@[path]
lemma asymptotic_bound_pointwise
  {C c b : ℝ}
  {n : ℕ}
  {pn : ℝ}
-- given
  (hc : 0 < c)
  (hn2 : 2 < n)
  (hn : (C + 1) / c ≤ pn * (n : ℝ) ^ (1/2 : ℝ) / Real.log ↑n)
  (hlarge : -(n : ℝ) ^ (3/2 : ℝ) * Real.log ↑n ≤ b) :
-- imply
  C * (n : ℝ) ^ (3/2 : ℝ) * Real.log ↑n - c * (n : ℝ) ^ 2 * pn ≤ b := by
-- proof
  have hn0 : (0 : ℝ) < n := by positivity
  have hnn : (1 : ℝ) < (n : ℝ) := by exact_mod_cast show 1 < n by omega
  have hlogn : 0 < Real.log ↑n := Real.log_pos hnn
  have hn32 : 0 < (n : ℝ) ^ (3/2 : ℝ) := rpow_pos_of_pos hn0 _
  have step1 : (C + 1) * Real.log ↑n ≤ c * (pn * (n : ℝ) ^ (1/2 : ℝ)) := by
    rw [div_le_div_iff₀ hc hlogn] at hn; linarith
  have step2 : (C + 1) * (n : ℝ) ^ (3/2 : ℝ) * Real.log ↑n ≤ c * pn * (n : ℝ) ^ 2 := by
    have h2 := mul_le_mul_of_nonneg_right step1 hn32.le
    have rpow_eq : (n : ℝ) ^ (1/2 : ℝ) * (n : ℝ) ^ (3/2 : ℝ) = (n : ℝ) ^ (2 : ℕ) := by
      rw [← rpow_add hn0, show (1:ℝ)/2 + 3/2 = (2 : ℕ) from by norm_num, rpow_natCast]
    calc (C + 1) * (n : ℝ) ^ (3/2 : ℝ) * Real.log ↑n
      = (C + 1) * Real.log ↑n * (n : ℝ) ^ (3/2 : ℝ) := by ring
      _ ≤ c * (pn * (n : ℝ) ^ (1/2 : ℝ)) * (n : ℝ) ^ (3/2 : ℝ) := h2
      _ = c * pn * ((n : ℝ) ^ (1/2 : ℝ) * (n : ℝ) ^ (3/2 : ℝ)) := by ring
      _ = c * pn * (n : ℝ) ^ 2 := by rw [rpow_eq]
  linarith [step2, hlarge]

end GraphContainers

namespace GraphContainers

/--
[exponent_tends_to_neg_inf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/GraphContainers.lean)
-/
@[path]
lemma exponent_tends_to_neg_inf
  {C c : ℝ}
  {p : ℕ → ℝ}
-- given
  (_hC : 0 < C)
  (hc : 0 < c)
  (hp_growth : Tendsto (fun n : ℕ => p n * (n : ℝ) ^ (1/2 : ℝ) / Real.log ↑n) atTop atTop) :
-- imply
  Tendsto (fun n : ℕ => C * (n : ℝ) ^ (3/2 : ℝ) * Real.log ↑n - c * (n : ℝ) ^ 2 * p n) atTop atBot := by
-- proof
  rw [tendsto_atBot]; intro b; rw [tendsto_atTop] at hp_growth
  obtain ⟨N1, hN1⟩ := (hp_growth ((C + 1) / c)).exists_forall_of_atTop
  have hN2 : ∃ N2 : ℕ, ∀ n : ℕ, N2 ≤ n → -(n : ℝ) ^ (3/2 : ℝ) * Real.log ↑n ≤ b := by
    by_cases hb : 0 ≤ b
    · exact ⟨3, fun n hn => by
      have : 0 ≤ (n : ℝ) ^ (3/2 : ℝ) * Real.log ↑n :=
        mul_nonneg (rpow_nonneg (Nat.cast_nonneg n) _)
          (le_of_lt (Real.log_pos (by exact_mod_cast show 1 < n by omega)))
      linarith⟩
    · push Not at hb
      refine ⟨max 3 (Nat.ceil (-b) + 1), fun n hn => ?_⟩
      have hn3 : 3 ≤ n := le_of_max_le_left hn
      have hn_ceil : Nat.ceil (-b) + 1 ≤ n := le_of_max_le_right hn
      have hn0 : (0 : ℝ) < n := by positivity
      have hnn : (1 : ℝ) < (n : ℝ) := by exact_mod_cast show 1 < n by omega
      have h_rpow_ge : (n : ℝ) ≤ (n : ℝ) ^ (3/2 : ℝ) := by
        conv_lhs => rw [show (n : ℝ) = (n : ℝ) ^ (1 : ℝ) from (rpow_one _).symm]
        exact rpow_le_rpow_of_exponent_le (le_of_lt hnn) (by norm_num : (1 : ℝ) ≤ 3/2)
      have h_log_ge : (1 : ℝ) ≤ Real.log ↑n := by
        have : Real.exp 1 ≤ (n : ℝ) := le_of_lt (calc Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
          _ < 3 := by norm_num
          _ ≤ (n : ℝ) := by exact_mod_cast hn3)
        rwa [Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < ↑n)]
      linarith [show -b < (n : ℝ) ^ (3/2 : ℝ) * Real.log ↑n from calc
        -b ≤ Nat.ceil (-b) := Nat.le_ceil (-b)
        _ < Nat.ceil (-b) + 1 := by linarith
        _ ≤ (n : ℝ) := by exact_mod_cast hn_ceil
        _ ≤ (n : ℝ) ^ (3/2 : ℝ) := h_rpow_ge
        _ = (n : ℝ) ^ (3/2 : ℝ) * 1 := by ring
        _ ≤ (n : ℝ) ^ (3/2 : ℝ) * Real.log ↑n :=
          mul_le_mul_of_nonneg_left h_log_ge (rpow_nonneg (Nat.cast_nonneg n) _)]
  obtain ⟨N2, hN2⟩ := hN2
  filter_upwards [Ioi_mem_atTop (max (max N1 N2) 2)] with n hn
  exact asymptotic_bound_pointwise C c b hc n (p n)
    (by have := Set.mem_Ioi.mp hn; omega) (hN1 n (by have := Set.mem_Ioi.mp hn; omega))
    (hN2 n (by have := Set.mem_Ioi.mp hn; omega))
/-- Mantel-in-random-graphs corollary: if $p_n n^{1/2}/\log n \to \infty$, then with
probability tending to $1$ every triangle-free subgraph of $G(n, p_n)$ has at most
$(1/4 + 2\varepsilon) p_n n^2$ edges. -/
end



-- created on 2026-10-23
