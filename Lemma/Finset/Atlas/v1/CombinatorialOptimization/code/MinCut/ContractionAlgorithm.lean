import Mathlib
import sympy.Basic
import Def.v1.Atlas.CombinatorialOptimization.code.MinCut.ContractionAlgorithm
open Finset MinCut


namespace MinCut

/--
[Multigraph.cutValue_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/MinCut/ContractionAlgorithm.lean)
-/
@[path]
lemma Multigraph.cutValue_singleton
  [Fintype V]
  [DecidableEq V]
  {G : Multigraph V}
  {v : V} :
-- imply
  G.cutValue {v} = G.degree v := by
-- proof
  simp only [cutValue, degree, Finset.sum_singleton]
  have h_compl : ({v} : Finset V)ᶜ = Finset.univ.erase v := by ext u; simp
  rw [h_compl]
  have := Finset.sum_erase_add Finset.univ (fun u => G.edgeMult v u) (Finset.mem_univ v)
  linarith [G.no_loops v]

end MinCut

namespace MinCut

/--
[Multigraph.degree_ge_minCut](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/MinCut/ContractionAlgorithm.lean)
-/
@[path]
lemma Multigraph.degree_ge_minCut
  [Fintype V]
  [DecidableEq V]
  {G : Multigraph V}
  {S : Finset V}
  {v : V}
-- given
  (hS : G.IsMinCut S)
  (hV : 2 ≤ Fintype.card V) :
-- imply
  G.cutValue S ≤ G.degree v := by
-- proof
  rw [← cutValue_singleton G v]
  exact hS.2.2 {v} (Finset.singleton_nonempty v) (by
    intro h
    have := Finset.card_singleton v
    rw [h, Finset.card_univ] at this
    omega)

end MinCut

namespace MinCut

/--
[Multigraph.sum_degrees_ge_card_mul_minCut](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/MinCut/ContractionAlgorithm.lean)
-/
@[path]
lemma Multigraph.sum_degrees_ge_card_mul_minCut
  [Fintype V]
  [DecidableEq V]
  {G : Multigraph V}
  {S : Finset V}
-- given
  (hS : G.IsMinCut S)
  (hV : 2 ≤ Fintype.card V) :
-- imply
  Fintype.card V * G.cutValue S ≤ ∑ v : V, G.degree v := by
-- proof
  calc Fintype.card V * G.cutValue S
    = ∑ _v : V, G.cutValue S := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ ≤ ∑ v : V, G.degree v :=
      Finset.sum_le_sum (fun v _ => degree_ge_minCut G S hS v hV)

end MinCut

namespace MinCut

/--
[Multigraph.mincut_edge_fraction_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/MinCut/ContractionAlgorithm.lean)
-/
@[path]
lemma Multigraph.mincut_edge_fraction_le
  [Fintype V]
  [DecidableEq V]
  {G : Multigraph V}
  {S : Finset V}
-- given
  (hS : G.IsMinCut S)
  (hV : 2 ≤ Fintype.card V)
  (hE : 0 < ∑ v : V, G.degree v) :
-- imply
  (G.cutValue S : ℝ) / ((∑ v : V, G.degree v : ℝ) / 2) ≤ 2 / (Fintype.card V : ℝ) := by
-- proof
  have hn_pos : (0 : ℝ) < (Fintype.card V : ℝ) := by positivity
  have hE_pos : (0 : ℝ) < (∑ v : V, (G.degree v : ℝ)) / 2 := by
    have : (0 : ℝ) < (∑ v : V, G.degree v : ℝ) := by exact_mod_cast hE
    linarith
  rw [div_le_div_iff₀ hE_pos hn_pos]
  have h_bound := sum_degrees_ge_card_mul_minCut G S hS hV
  have h_cast := @Nat.cast_le ℝ _ |>.mpr h_bound
  push_cast at h_cast ⊢
  linarith

end MinCut

namespace MinCut

/--
[prod_range_sub_cast_eq_descFactorial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/MinCut/ContractionAlgorithm.lean)
-/
@[path]
lemma prod_range_sub_cast_eq_descFactorial
  [Fintype V]
  [DecidableEq V]
  {n m : ℕ}
-- given
  (h : m ≤ n) :
-- imply
  ∏ i ∈ Finset.range m, ((n : ℝ) - ↑i) = ↑(n.descFactorial m) := by
-- proof
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [Nat.cast_sub (by omega : i ≤ n)]

end MinCut

namespace MinCut

/--
[contraction_survival_product_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/MinCut/ContractionAlgorithm.lean)
-/
@[path]
lemma contraction_survival_product_eq
  [Fintype V]
  [DecidableEq V]
  {n : ℕ}
-- given
  (hn : 2 ≤ n) :
-- imply
  ∏ i ∈ Finset.range (n - 2), ((n : ℝ) - ↑i - 2) / ((n : ℝ) - ↑i) = 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
-- proof
  rw [Finset.prod_div_distrib]
  have hnum : ∀ i ∈ Finset.range (n - 2), ((n : ℝ) - ↑i - 2) = ((n - 2 : ℕ) : ℝ) - ↑i := by
    intro i hi
    rw [Finset.mem_range] at hi
    push_cast [Nat.cast_sub (by omega : 2 ≤ n)]
    ring
  rw [Finset.prod_congr rfl hnum]
  rw [prod_range_sub_cast_eq_descFactorial (n - 2) (n - 2) (le_refl _)]
  rw [Nat.descFactorial_self]
  rw [prod_range_sub_cast_eq_descFactorial n (n - 2) (by omega)]
  rw [Nat.descFactorial_eq_div (by omega : n - 2 ≤ n)]
  rw [show n - (n - 2) = 2 from by omega]
  rw [Nat.cast_div (Nat.factorial_dvd_factorial (by omega : 2 ≤ n)) (by positivity)]
  norm_num
  rw [div_div_eq_mul_div, mul_comm]
  have key : (↑n.factorial : ℝ) = ↑n * (↑n - 1) * ↑(n - 2).factorial := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    simp only [show m + 2 - 2 = m from by omega]
    rw [show Nat.factorial (m + 2) = (m + 2) * (m + 1) * Nat.factorial m from by
      rw [Nat.factorial_succ, Nat.factorial_succ]; ring]
    push_cast; ring
  rw [key]
  field_simp

end MinCut

namespace MinCut

/--
[contraction_survival_product_one_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/MinCut/ContractionAlgorithm.lean)
-/
@[path]
lemma contraction_survival_product_one_sub
  [Fintype V]
  [DecidableEq V]
  {n : ℕ}
-- given
  (hn : 2 ≤ n) :
-- imply
  ∏ i ∈ Finset.range (n - 2), (1 - 2 / ((n : ℝ) - ↑i)) = 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
-- proof
  have h : ∀ i ∈ Finset.range (n - 2),
    1 - 2 / ((n : ℝ) - ↑i) = ((n : ℝ) - ↑i - 2) / ((n : ℝ) - ↑i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hni : (0 : ℝ) < (n : ℝ) - ↑i := by
      have : (i : ℝ) < ↑n := by exact_mod_cast show i < n from by omega
      linarith
    rw [sub_div, div_self (ne_of_gt hni)]
  rw [Finset.prod_congr rfl h]
  exact contraction_survival_product_eq n hn

end MinCut

namespace MinCut

/--
[Multigraph.contractionSurvivalProb_ge_prod](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/MinCut/ContractionAlgorithm.lean)
-/
@[path]
lemma Multigraph.contractionSurvivalProb_ge_prod
  [Fintype V]
  [DecidableEq V]
  {G : Multigraph V}
  {S : Finset V}
-- given
  (hS : G.IsMinCut S)
  (hV : 2 ≤ Fintype.card V) :
-- imply
  G.contractionSurvivalProb S ≥ ∏ i ∈ Finset.range (Fintype.card V - 2), (1 - 2 / ((Fintype.card V : ℝ) - ↑i)) := by
-- proof
  unfold Multigraph.contractionSurvivalProb
  set n := Fintype.card V
  set c := 1 - (G.cutValue S : ℝ) / ((∑ v : V, G.degree v : ℝ) / 2)
  have hc_bound : c ≥ 1 - 2 / (n : ℝ) := by
    by_cases hE : (0 : ℕ) < ∑ v : V, G.degree v
    · have h_frac := mincut_edge_fraction_le G S hS hV hE
      show 1 - 2 / (↑n : ℝ) ≤ c
      show 1 - 2 / (↑n : ℝ) ≤ 1 - (G.cutValue S : ℝ) / ((∑ v : V, G.degree v : ℝ) / 2)
      linarith
    · push_neg at hE
      have hE0 : (∑ v : V, G.degree v : ℕ) = 0 := Nat.eq_zero_of_le_zero hE
      show 1 - 2 / (↑n : ℝ) ≤ c
      show 1 - 2 / (↑n : ℝ) ≤ 1 - (G.cutValue S : ℝ) / ((∑ v : V, G.degree v : ℝ) / 2)
      have h_sum_zero : (∑ v : V, (G.degree v : ℝ)) = 0 := by exact_mod_cast hE0
      simp only [h_sum_zero, zero_div, div_zero, sub_zero]
      have : (2 : ℝ) / (↑n : ℝ) ≥ 0 := by positivity
      linarith
  have h_base_nonneg : (0 : ℝ) ≤ 1 - 2 / (n : ℝ) := by
    rw [sub_nonneg, div_le_one (by positivity : (0:ℝ) < ↑n)]
    exact_mod_cast hV
  have h_pow : (1 - 2 / (↑n : ℝ)) ^ (n - 2) ≤ c ^ (n - 2) :=
    pow_le_pow_left₀ h_base_nonneg hc_bound.le (n - 2)
  have h_prod : (1 - 2 / (n : ℝ)) ^ (n - 2) =
    ∏ _i ∈ Finset.range (n - 2), (1 - 2 / (n : ℝ)) := by
    simp [Finset.prod_const, Finset.card_range]
  have h_prod_le : ∏ i ∈ Finset.range (n - 2), (1 - 2 / ((n : ℝ) - ↑i)) ≤
    (1 - 2 / (n : ℝ)) ^ (n - 2) := by
    rw [h_prod]
    apply Finset.prod_le_prod
    · intro i hi
      rw [Finset.mem_range] at hi
      have hni : (2 : ℝ) < (n : ℝ) - ↑i := by
        have h1 : (i : ℝ) < (n : ℝ) - 2 := by exact_mod_cast show i < n - 2 from hi
        linarith
      rw [sub_nonneg, div_le_one (by linarith)]
      linarith
    · intro i hi
      rw [Finset.mem_range] at hi
      have hni : (0 : ℝ) < (n : ℝ) - ↑i := by
        have : (i : ℝ) < (n : ℝ) := by exact_mod_cast show i < n from by omega
        linarith
      have h_le : (2 : ℝ) / (n : ℝ) ≤ 2 / ((n : ℝ) - ↑i) := by
        apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2) hni
        have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
        linarith
      linarith
  linarith

end MinCut

namespace MinCut

/--
[contraction_algorithm_success_prob](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/MinCut/ContractionAlgorithm.lean)
-/
@[path]
lemma contraction_algorithm_success_prob
  [Fintype V]
  [DecidableEq V]
  {G : Multigraph V}
  {S : Finset V}
-- given
  (hS : G.IsMinCut S)
  (hV : 2 ≤ Fintype.card V) :
-- imply
  G.contractionSurvivalProb S ≥ 2 / ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) := by
-- proof
  have h_decomp := Multigraph.contractionSurvivalProb_ge_prod G S hS hV
  rwa [contraction_survival_product_one_sub (Fintype.card V) hV] at h_decomp

end MinCut


-- created on 2026-10-23
