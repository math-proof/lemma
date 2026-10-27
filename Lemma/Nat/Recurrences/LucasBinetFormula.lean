import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.LucasSequence
import Lemma.Nat.LucasSequence


namespace MetaMathlibExt

/--
[lucas_binet_aux_mul_pow_pred](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/LucasBinetFormula.lean)
-/
@[path]
private lemma lucas_binet_aux_mul_pow_pred {K : Type*} [Field K] (alpha : K) (m : ℕ) :
  (m : K) * alpha ^ (m - 1) * alpha = (m : K) * alpha ^ m := by
  cases m with
  | zero => simp
  | succ m => rw [Nat.add_sub_cancel]; ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lucas_binet_formulas_of_field](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/LucasBinetFormula.lean)
-/
@[path]
lemma lucas_binet_formulas_of_field
  [Field K]
  {params : LucasSequenceParams}
  {alpha beta : K}
-- given
  (hsum : alpha + beta = (params.p : K))
  (hprod : alpha * beta = (params.q : K)) :
-- imply
  (alpha ≠ beta → ∀ n : ℕ,
    (lucasU params n : K) = (alpha ^ n - beta ^ n) / (alpha - beta) ∧
    (lucasV params n : K) = alpha ^ n + beta ^ n) ∧
    (beta = alpha → ∀ n : ℕ,
    (lucasU params n : K) = (n : K) * alpha ^ (n - 1) ∧
    (lucasV params n : K) = 2 * alpha ^ n) := by
-- proof
  constructor
  · intro hne n
    have hsub : alpha - beta ≠ 0 := sub_ne_zero.mpr hne
    induction n using Nat.twoStepInduction with
    | zero =>
      constructor
      · simp [lucasU]
      · simp [lucasV, pow_zero, one_add_one_eq_two]
    | one =>
      constructor
      · simp [lucasU, pow_one, div_self hsub]
      · simp [lucasV, ← hsum, pow_one]
    | more n ih1 ih2 =>
      obtain ⟨ihU0, ihV0⟩ := ih1
      obtain ⟨ihU1, ihV1⟩ := ih2
      have hU : (lucasU params (n + 2) : K)
        = (params.p : K) * (lucasU params (n + 1) : K)
          - (params.q : K) * (lucasU params n : K) := by
        simp [lucasU, Int.cast_sub, Int.cast_mul]
      have hV : (lucasV params (n + 2) : K)
        = (params.p : K) * (lucasV params (n + 1) : K)
          - (params.q : K) * (lucasV params n : K) := by
        simp [lucasV, Int.cast_sub, Int.cast_mul]
      rw [← hsum, ← hprod] at hU hV
      constructor
      · rw [hU, ihU1, ihU0]
        field_simp
        ring
      · rw [hV, ihV1, ihV0]
        ring
  · intro hbeta n
    have hP : (params.p : K) = 2 * alpha := by rw [← hsum, hbeta]; ring
    have hQ : (params.q : K) = alpha ^ 2 := by rw [← hprod, hbeta]; ring
    induction n using Nat.twoStepInduction with
    | zero =>
      constructor
      · simp [lucasU]
      · simp [lucasV, pow_zero]
    | one =>
      constructor
      · simp [lucasU]
      · simp [lucasV, hP, pow_one]
    | more n ih1 ih2 =>
      obtain ⟨ihU0, ihV0⟩ := ih1
      obtain ⟨ihU1, ihV1⟩ := ih2
      have hU : (lucasU params (n + 2) : K)
        = (params.p : K) * (lucasU params (n + 1) : K)
          - (params.q : K) * (lucasU params n : K) := by
        simp [lucasU, Int.cast_sub, Int.cast_mul]
      have hV : (lucasV params (n + 2) : K)
        = (params.p : K) * (lucasV params (n + 1) : K)
          - (params.q : K) * (lucasV params n : K) := by
        simp [lucasV, Int.cast_sub, Int.cast_mul]
      rw [hP, hQ] at hU hV
      have e1 : n + 1 - 1 = n := by omega
      have e2 : n + 2 - 1 = n + 1 := by omega
      rw [e1] at ihU1
      have hpow : alpha ^ 2 * ((n : K) * alpha ^ (n - 1))
        = alpha * ((n : K) * alpha ^ n) := by
        have h := lucas_binet_aux_mul_pow_pred alpha n
        rw [pow_two]
        linear_combination alpha * h
      constructor
      · rw [hU, ihU1, ihU0, e2, hpow]
        push_cast
        ring
      · rw [hV, ihV1, ihV0]
        ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lucas_binet_formulas](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/LucasBinetFormula.lean)
-/
@[path]
lemma lucas_binet_formulas
  [Field K] [CharZero K]
  {params : LucasSequenceParams}
  {alpha beta : K}
-- given
  (hsum : alpha + beta = (params.p : K))
  (hprod : alpha * beta = (params.q : K)) :
-- imply
  (alpha ≠ beta → ∀ n : ℕ,
    (lucasU params n : K) = (alpha ^ n - beta ^ n) / (alpha - beta) ∧
    (lucasV params n : K) = alpha ^ n + beta ^ n) ∧
    (beta = alpha → ∀ n : ℕ,
    (lucasU params n : K) = (n : K) * alpha ^ (n - 1) ∧
    (lucasV params n : K) = 2 * alpha ^ n) :=
-- proof
  lucas_binet_formulas_of_field params alpha beta hsum hprod
end



-- created on 2026-10-20
-- updated on 2026-10-26
