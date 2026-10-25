import Mathlib
import sympy.Basic
import Def.Combinatorics.Enumerative.RisingDiagonalSequence
open MetaMathlibExt


namespace MetaMathlibExt

/--
[risingDiagonal_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RisingDiagonalSequence.lean)
-/
@[path]
column-zero tail: if `2 * k ≤ n` then `a (n - k) k = a n 0`. -/
private lemma risingDiagonal_aux {a : ℕ → ℕ → ℝ} {a₀ a₁ α β : ℝ}
  (h : IsBinaryBinomialInterpolatedTriangle a a₀ a₁ α β) (k : ℕ) :
  ∀ n : ℕ, 2 * k ≤ n → a (n - k) k = a n 0 := by
  induction k with
  | zero =>
    intro n _
    simp
  | succ k ih =>
    intro n hn
    have h0rec : ∀ m : ℕ, 2 ≤ m →
      a m 0 = α * a (m - 1) 0 + β * a (m - 2) 0 :=
      h.2.2.2.2.1
    have hrec : ∀ m l : ℕ, 1 ≤ l → l ≤ m →
      a m l = α * a m (l - 1) + β * a (m - 1) (l - 1) :=
      h.2.2.2.2.2
    -- The recurrence applies at row `n - (k + 1)`, whose index still
    -- dominates `k + 1` because `2 * (k + 1) ≤ n`.
    have hle : k + 1 ≤ n - (k + 1) := by omega
    have hstep := hrec (n - (k + 1)) (k + 1) (by omega) hle
    rw [Nat.add_sub_cancel] at hstep
    -- Reindex both summands so the induction hypothesis applies at
    -- levels `n - 1` and `n - 2`; each rewrite is valid since `n ≥ 2`.
    have e1 : n - (k + 1) = (n - 1) - k := by omega
    have e2 : n - (k + 1) - 1 = (n - 2) - k := by omega
    have t1 : a (n - (k + 1)) k = a (n - 1) 0 := by
      rw [e1]
      exact ih (n - 1) (by omega)
    have t2 : a (n - (k + 1) - 1) k = a (n - 2) 0 := by
      rw [e2]
      exact ih (n - 2) (by omega)
    have hn0 : a n 0 = α * a (n - 1) 0 + β * a (n - 2) 0 :=
      h0rec n (by omega)
    rwa [hstep, t1, t2]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[risingDiagonal_const](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RisingDiagonalSequence.lean)
-/
@[path]
lemma risingDiagonal_const
  {a : ℕ → ℕ → ℝ}
  {a₀ a₁ α β : ℝ}
  {n : ℕ}
  {i j : Fin (n / 2 + 1)}
-- given
  (h : IsBinaryBinomialInterpolatedTriangle a a₀ a₁ α β) :
-- imply
  risingDiagonal a n i = risingDiagonal a n j := by
-- proof
  -- Fin bounds give `2 * i ≤ n` and `2 * j ≤ n` via `omega` on `n / 2`.
  have hi2 : 2 * (i : ℕ) ≤ n := by
    have hilt := i.isLt
    omega
  have hj2 : 2 * (j : ℕ) ≤ n := by
    have hjlt := j.isLt
    omega
  change a (n - (i : ℕ)) (i : ℕ) = a (n - (j : ℕ)) (j : ℕ)
  exact (risingDiagonal_aux h i n hi2).trans (risingDiagonal_aux h j n hj2).symm

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
