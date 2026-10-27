import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MetaMathlibExt

/--
[associated_pell_cassini_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/AssociatedPellCassini.lean)
-/
@[path]
lemma associated_pell_cassini_identity
  {Q : ℕ → ℤ}
  {k : ℕ}
-- given
  (hQ_zero : Q 0 = 1)
  (hQ_one : Q 1 = 1)
  (hQ_rec : ∀ n : ℕ, Q (n + 2) = 2 * Q (n + 1) + Q n)
  (hk : 1 ≤ k) :
-- imply
  Q (k - 1) * Q (k + 1) =
      Q k ^ 2 + 2 * (-1 : ℤ) ^ (k - 1) := by
-- proof
  have r0 : Q 2 = 2 * Q 1 + Q 0 := hQ_rec 0
  have base : Q 0 * Q 2 - Q 1 ^ 2 = 2 * (-1 : ℤ) ^ 0 := by
    rw [hQ_zero, hQ_one, r0, hQ_zero, hQ_one]
    norm_num
  have step : ∀ j, Q (j + 1) * Q (j + 3) - Q (j + 2) ^ 2 =
    -(Q j * Q (j + 2) - Q (j + 1) ^ 2) := by
    intro j
    have r1 := hQ_rec j
    have r2 := hQ_rec (j + 1)
    have e1 : j + 1 + 2 = j + 3 := by omega
    have e2 : j + 1 + 1 = j + 2 := by omega
    rw [e1, e2] at r2
    linear_combination (Q (j + 1)) * r2 - (Q (j + 2)) * r1
  have E : ∀ j, Q j * Q (j + 2) - Q (j + 1) ^ 2 = 2 * (-1 : ℤ) ^ j := by
    intro j
    induction j with
    | zero =>
      have e1 : 0 + 2 = 2 := by omega
      have e2 : 0 + 1 = 1 := by omega
      rwa [e1, e2]
    | succ j ih =>
      have e1 : j + 1 + 2 = j + 3 := by omega
      have e2 : j + 1 + 1 = j + 2 := by omega
      rw [e1, e2]
      have pw : (-1 : ℤ) ^ (j + 1) = -(-1 : ℤ) ^ j := by
        rw [pow_succ]
        ring
      rw [step j, ih, pw]
      ring
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have e0 : 1 + m = m + 1 := by omega
  have e1 : 1 + m - 1 = m := by omega
  have e2 : 1 + m + 1 = m + 2 := by omega
  rw [e1, e2, e0]
  have hE := E m
  linear_combination hE

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
