import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.LogSpace
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.LogSpace
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.HierarchyTheorems
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.HierarchyTheorems
open SpaceComplexity LogSpace TuringMachine


namespace NLStrictPSPACE

/--
[nl_subset_space_log_squared](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NLStrictPSPACE.lean)
-/
@[path]
lemma nl_subset_space_log_squared
  {Γ : Type}
  {A : Set (List Γ)}
-- given
  (hA : InNL A) :
-- imply
  InSPACE (fun n => (Nat.log 2 n) ^ 2) A :=
-- proof
  LogSpace.nl_subset_space_log2 A hA

end NLStrictPSPACE

namespace NLStrictPSPACE

/--
[two_pow_gt_cube](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NLStrictPSPACE.lean)
-/
@[path]
lemma two_pow_gt_cube
  {m : ℕ}
-- given
  (hm : 10 ≤ m) :
-- imply
  m ^ 3 < 2 ^ m := by
-- proof
  induction m with
  | zero => omega
  | succ n ih =>
    by_cases hn : 10 ≤ n
    · have ih' := ih hn
      have h1 : (n + 1) ^ 3 = n ^ 3 + 3 * n ^ 2 + 3 * n + 1 := by ring
      have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      rw [h1, h2]
      have h3 : 3 * n ^ 2 + 3 * n + 1 ≤ n ^ 3 := by nlinarith
      linarith
    · interval_cases n <;> omega

end NLStrictPSPACE

namespace NLStrictPSPACE

/--
[log_sq_little_o_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NLStrictPSPACE.lean)
-/
@[path]
lemma log_sq_little_o_id
-- imply
  IsAsympDominated (fun n => (Nat.log 2 n) ^ 2) (fun n => n) := by
-- proof
  intro c hc
  use 2 ^ (max 10 (c + 1))
  intro n hn
  have hn_pos : 0 < n := by
    calc (0 : ℕ) < 2 ^ max 10 (c + 1) := by positivity
      _ ≤ n := hn
  have hn_ne : n ≠ 0 := by omega
  set m := Nat.log 2 n with hm_def
  have h_pow_le : 2 ^ m ≤ n := Nat.pow_log_le_self 2 hn_ne
  have h_m_ge : max 10 (c + 1) ≤ m := by
    rw [hm_def]
    calc max 10 (c + 1)
      = Nat.log 2 (2 ^ max 10 (c + 1)) :=
        (Nat.log_pow (by norm_num : (1 : ℕ) < 2) _).symm
      _ ≤ Nat.log 2 n := Nat.log_mono_right hn
  have h_m_ge_10 : 10 ≤ m := le_trans (le_max_left 10 (c + 1)) h_m_ge
  have h_c_lt_m : c < m := by omega
  have h1 : c * m ^ 2 < m ^ 3 := by
    calc c * m ^ 2 < m * m ^ 2 :=
      Nat.mul_lt_mul_of_pos_right h_c_lt_m (by positivity)
      _ = m ^ 3 := by ring
  have h2 : m ^ 3 < 2 ^ m := two_pow_gt_cube m h_m_ge_10
  show c * (Nat.log 2 n) ^ 2 < n
  rw [← hm_def]
  linarith

end NLStrictPSPACE

namespace NLStrictPSPACE

/--
[isAsympBoundedBy_trans_isAsympDominated](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NLStrictPSPACE.lean)
-/
@[path]
lemma isAsympBoundedBy_trans_isAsympDominated
  {g h f : ℕ → ℕ}
-- given
  (hgh : IsAsympBoundedBy g h)
  (hhf : IsAsympDominated h f) :
-- imply
  IsAsympDominated g f := by
-- proof
  intro c hc
  obtain ⟨C, n₁, hC, hg⟩ := hgh
  obtain ⟨n₂, hh⟩ := hhf (c * C) (Nat.mul_pos hc hC)
  use max n₁ n₂
  intro n hn
  have hn₁ : n₁ ≤ n := le_of_max_le_left hn
  have hn₂ : n₂ ≤ n := le_of_max_le_right hn
  have hstep1 : c * g n ≤ c * (C * h n) := Nat.mul_le_mul_left c (hg n hn₁)
  have hstep2 : c * (C * h n) = c * C * h n := by ring
  have hstep3 : c * C * h n < f n := hh n hn₂
  linarith

end NLStrictPSPACE

namespace NLStrictPSPACE

/--
[log_sq_le_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NLStrictPSPACE.lean)
-/
@[path]
lemma log_sq_le_sq
  {n : ℕ} :
-- imply
  (Nat.log 2 n) ^ 2 ≤ n ^ 2 :=
-- proof
  Nat.pow_le_pow_left (Nat.log_le_self 2 n) 2

end NLStrictPSPACE

namespace NLStrictPSPACE

/--
[space_log_sq_subset_pspace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NLStrictPSPACE.lean)
-/
@[path]
lemma space_log_sq_subset_pspace
  {Γ : Type}
  {A : Set (List Γ)}
-- given
  (hA : InSPACE (fun n => (Nat.log 2 n) ^ 2) A) :
-- imply
  InPSPACE A := by
-- proof
  obtain ⟨Q, _, hQ, M, hL, g, ⟨C, n₀, hC, hg⟩, hM⟩ := hA
  refine ⟨2, Q, inferInstance, hQ, M, hL, g, ⟨C, n₀, hC, fun n hn => ?_⟩, hM⟩
  calc g n ≤ C * (Nat.log 2 n) ^ 2 := hg n hn
    _ ≤ C * n ^ 2 := Nat.mul_le_mul_left C (log_sq_le_sq n)

end NLStrictPSPACE

namespace NLStrictPSPACE

/--
[nl_subset_pspace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NLStrictPSPACE.lean)
-/
@[path]
lemma nl_subset_pspace
  {Γ : Type}
  {A : Set (List Γ)}
-- given
  (hA : InNL A) :
-- imply
  InPSPACE A :=
-- proof
  space_log_sq_subset_pspace A (nl_subset_space_log_squared A hA)

end NLStrictPSPACE

namespace NLStrictPSPACE

/--
[log_sq_little_o_succ2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NLStrictPSPACE.lean)
-/
@[path]
lemma log_sq_little_o_succ2
-- imply
  IsAsympDominated (fun n => (Nat.log 2 n) ^ 2) (fun n => n + 2) := by
-- proof
  intro c hc
  obtain ⟨n₀, hn₀⟩ := log_sq_little_o_id c hc
  use n₀
  intro n hn
  have h := hn₀ n hn
  linarith

end NLStrictPSPACE

namespace NLStrictPSPACE

/--
[space_log_sq_in_spaceo_succ2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NLStrictPSPACE.lean)
-/
@[path]
lemma space_log_sq_in_spaceo_succ2
  {Γ : Type}
  {A : Set (List Γ)}
-- given
  (hA : InSPACE (fun n => (Nat.log 2 n) ^ 2) A) :
-- imply
  InSPACEo (fun n => n + 2) A := by
-- proof
  obtain ⟨Q, _, hQ, M, hL, g, hglog, hM⟩ := hA
  exact ⟨Q, inferInstance, hQ, M, hL, g,
    isAsympBoundedBy_trans_isAsympDominated hglog log_sq_little_o_succ2, hM⟩

end NLStrictPSPACE

namespace NLStrictPSPACE

/--
[space_succ2_subset_pspace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NLStrictPSPACE.lean)
-/
@[path]
lemma space_succ2_subset_pspace
  {Γ : Type}
  {A : Set (List Γ)}
-- given
  (hA : InSPACE (fun n => n + 2) A) :
-- imply
  InPSPACE A := by
-- proof
  obtain ⟨Q, _, hQ, M, hL, g, ⟨C, n₀, hC, hg⟩, hM⟩ := hA
  refine ⟨2, Q, inferInstance, hQ, M, hL, g, ⟨C, max n₀ 3, hC, fun n hn => ?_⟩, hM⟩
  have hn₀ : n₀ ≤ n := le_of_max_le_left hn
  have hn3 : 3 ≤ n := le_of_max_le_right hn
  have h_bound : n + 2 ≤ n ^ 2 := by nlinarith
  calc g n ≤ C * (n + 2) := hg n hn₀
    _ ≤ C * n ^ 2 := Nat.mul_le_mul_left C h_bound
/-- **Corollary (Sipser, Review of Hierarchy Theorems).** `NL ⊊ PSPACE`.
Concretely we prove the two parts of strict inclusion:
1. Every `NL` language lies in `PSPACE`.
2. There exists a `PSPACE` language not in `NL`, obtained from the Space Hierarchy Theorem at
  the bound `n + 2` (which is space-constructible). Any `NL` language is in `SPACE(log² n)`,
  hence in `SPACEo(n + 2)`, contradicting the hierarchy separation. -/

end NLStrictPSPACE


-- created on 2026-10-23
