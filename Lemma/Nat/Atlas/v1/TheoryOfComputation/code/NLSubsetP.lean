import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TheoryOfComputation.code.LogSpace.Part4
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.LogSpace
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.ConfigReachability
import Def.v1.Atlas.TheoryOfComputation.code.ConfigReachability
open SpaceComplexity LogSpace TuringMachine


namespace NLSubsetP

/--
[nspace_log_config_graph_poly_time_decidable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NLSubsetP.lean)
-/
@[path]
lemma nspace_log_config_graph_poly_time_decidable
  {Γ : Type}
  {A : Set (List Γ)}
  {Q : Type}
  [DecidableEq Q]
  {M : SpaceComplexity.NTM Q Γ}
  {g : ℕ → ℕ}
-- given
  (hLang : M.language = A)
  (hgBound : IsAsympBoundedBy g log)
  (hSpace : M.RunsInSpace g) :
-- imply
  InP A := by
-- proof
  obtain ⟨Q', _, hDecEq', T, t, K, hDecides, hRunsInTime, hK_pos, htBound⟩ :=
    nspace_bounded_decider_poly_time M g hSpace
  obtain ⟨c_bound, n₀, hc_pos, hgBoundFn⟩ := hgBound
  have hDecidesA : T.decides A := hLang ▸ hDecides
  use K * c_bound + 1
  exact ⟨Q', inferInstance, hDecEq', T, t, hDecidesA, hRunsInTime,
    ⟨K, max n₀ 1, hK_pos, fun n hn => by
      dsimp only at hn ⊢
      have hn₀ : n₀ ≤ n := le_of_max_le_left hn
      have hn1 : 1 ≤ n := le_of_max_le_right hn
      have hn0 : n ≠ 0 := by omega
      have hg_le : g n ≤ c_bound * Nat.log 2 n := by
        have := hgBoundFn n hn₀; simp only [log] at this; exact this
      calc t n ≤ K * 2 ^ (K * g n) := htBound n
        _ ≤ K * 2 ^ (K * (c_bound * Nat.log 2 n)) := by
          apply Nat.mul_le_mul_left
          apply Nat.pow_le_pow_right (by norm_num : 1 ≤ 2)
          apply Nat.mul_le_mul_left
          exact hg_le
        _ = K * (2 ^ Nat.log 2 n) ^ (K * c_bound) := by
          rw [← pow_mul]; congr 1
          rw [mul_comm c_bound, ← mul_assoc, mul_comm K, mul_assoc]
        _ ≤ K * n ^ (K * c_bound) :=
          Nat.mul_le_mul_left K (Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hn0) _)
        _ ≤ K * n ^ (K * c_bound + 1) :=
          Nat.mul_le_mul_left K (Nat.pow_le_pow_right hn1 (Nat.le_succ _))⟩⟩

end NLSubsetP

namespace NLSubsetP

/--
[nl_subset_p](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NLSubsetP.lean)
-/
@[path]
lemma nl_subset_p
  {Γ : Type}
  {A : Set (List Γ)}
-- given
  (hA : InNL A) :
-- imply
  InP A := by
-- proof
  unfold InNL InNSPACE at hA
  obtain ⟨Q, _, hDecEq, M, hLang, g, hgBound, hSpace⟩ := hA
  exact @nspace_log_config_graph_poly_time_decidable Γ A Q hDecEq M hLang g hgBound hSpace

end NLSubsetP


-- created on 2026-10-23
