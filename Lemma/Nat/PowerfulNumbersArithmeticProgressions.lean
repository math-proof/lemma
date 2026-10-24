import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.KFull
import Lemma.Nat.KFull


namespace MetaMathlibExt

/--
[arbitrarily_long_arithmetic_progressions_of_powerful_numbers_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PowerfulNumbersArithmeticProgressions.lean)
-/
@[path]
lemma arbitrarily_long_arithmetic_progressions_of_powerful_numbers_general
  {k : ℕ} :
-- imply
  ∃ a d : ℕ, 0 < a ∧ 0 < d ∧
    ∀ i : ℕ, i < k → Nat.IsKFull 2 (a + i * d) := by
-- proof
  -- Let L be a common multiple of 1, 2, ..., k; use N_i = 1 + i and M_i = L^2 * N_i.
  set L : ℕ := ∏ j ∈ Finset.range k, (1 + j) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]
    apply Finset.prod_pos
    intro j _
    omega
  have ha : 0 < L ^ 2 := pow_pos hLpos 2
  refine ⟨L ^ 2, L ^ 2, ha, ha, fun i hi => ⟨(Nat.add_pos_left ha _).ne', fun p hp hdvd => ?_⟩⟩
  have hmem : (1 + i) ∣ L := Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hi)
  have heq : L ^ 2 + i * L ^ 2 = L ^ 2 * (1 + i) := by ring
  rw [heq] at hdvd ⊢
  have hpL : p ∣ L := by
    obtain h | h := (hp.dvd_mul.mp hdvd)
    · exact hp.dvd_of_dvd_pow h
    · exact h.trans hmem
  exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hpL 2) _
set_option linter.unusedVariables false in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[arbitrarily_long_arithmetic_progressions_of_powerful_numbers](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PowerfulNumbersArithmeticProgressions.lean)
-/
@[path]
lemma arbitrarily_long_arithmetic_progressions_of_powerful_numbers
  {k : ℕ}
-- given
  (hk : 3 ≤ k) :
-- imply
  ∃ a d : ℕ, 0 < a ∧ 0 < d ∧
    ∀ i : ℕ, i < k →
    ∀ p : ℕ, p.Prime → p ∣ a + i * d → p ^ 2 ∣ a + i * d := by
-- proof
  obtain ⟨a, d, ha, hd, h⟩ := arbitrarily_long_arithmetic_progressions_of_powerful_numbers_general k
  exact ⟨a, d, ha, hd, fun i hi => (h i hi).2⟩

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
