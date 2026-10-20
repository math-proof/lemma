/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/LucasBinetFormula.lean -/

import sympy.atlas.NumberTheory.LucasSequence
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

section
/-- `m * alpha ^ (m - 1) * alpha = m * alpha ^ m`; at `m = 0` both sides vanish. -/
private theorem lucas_binet_aux_mul_pow_pred {K : Type*} [Field K] (alpha : K) (m : ℕ) :
    (m : K) * alpha ^ (m - 1) * alpha = (m : K) * alpha ^ m := by
  cases m with
  | zero => simp
  | succ m => rw [Nat.add_sub_cancel]; ring

/-- Binet formulas for the Lucas sequences `U(P, Q)` and `V(P, Q)` over an arbitrary field,
e.g. `ZMod p`; see `lucas_binet_formulas`. In positive characteristic the coefficient `n` of the
double-root formula is read modulo the characteristic. -/
theorem lucas_binet_formulas_of_field
    {K : Type*} [Field K]
    (params : LucasSequenceParams) (alpha beta : K)
    (hsum : alpha + beta = (params.p : K))
    (hprod : alpha * beta = (params.q : K)) :
    (alpha ≠ beta → ∀ n : ℕ,
      (lucasU params n : K) = (alpha ^ n - beta ^ n) / (alpha - beta) ∧
      (lucasV params n : K) = alpha ^ n + beta ^ n) ∧
    (beta = alpha → ∀ n : ℕ,
      (lucasU params n : K) = (n : K) * alpha ^ (n - 1) ∧
      (lucasV params n : K) = 2 * alpha ^ n) := by
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

/-- Binet formulas for the Lucas sequences `U(P, Q)` and `V(P, Q)`.

Distinct-root case (`alpha ≠ beta`): with `alpha + beta = P` and
`alpha * beta = Q`, one has `Uₙ = (alpha ^ n - beta ^ n) / (alpha - beta)`
and `Vₙ = alpha ^ n + beta ^ n` for all `n`.

Double-root case (`beta = alpha`): then `P = 2 * alpha` and `Q = alpha ^ 2`,
and the formulas degenerate to `Uₙ = n * alpha ^ (n - 1)` and
`Vₙ = 2 * alpha ^ n` for all `n`. The natural subtraction in `n - 1` is
harmless at `n = 0` because the coefficient `(n : K)` is zero there.

Provenance: Christian Ballot, "A Further Generalization of a Congruence of
Wolstenholme", Journal of Integer Sequences 15 (2012), Article 12.8.6,
sequence definitions and formulas at lines 274–289,
https://cs.uwaterloo.ca/journals/JIS/VOL15/Ballot/ballot4.tex
complete-source SHA-256
`b96be332c67702b765cf4d73089ecb09c1e544c95afec737b8ff1445e4bffa17`;
normalized lines 274–289 SHA-256
`a1f6755e5072c434c537d1e8c874715fad642cdc2f3ecae191f676022d222a5e`;
normalized formula lines 283–289 SHA-256
`955c225b2d2be3f81e25044e2179816a66f1923c22b4b40bf21c9cdef276e0c9`.

Proves `Wanted` entry `lucas_binet_formulas`.
-/
theorem lucas_binet_formulas
    {K : Type*} [Field K] [CharZero K]
    (params : LucasSequenceParams) (alpha beta : K)
    (hsum : alpha + beta = (params.p : K))
    (hprod : alpha * beta = (params.q : K)) :
    (alpha ≠ beta → ∀ n : ℕ,
      (lucasU params n : K) = (alpha ^ n - beta ^ n) / (alpha - beta) ∧
      (lucasV params n : K) = alpha ^ n + beta ^ n) ∧
    (beta = alpha → ∀ n : ℕ,
      (lucasU params n : K) = (n : K) * alpha ^ (n - 1) ∧
      (lucasV params n : K) = 2 * alpha ^ n) :=
  lucas_binet_formulas_of_field params alpha beta hsum hprod

end

end MetaMathlibExt
