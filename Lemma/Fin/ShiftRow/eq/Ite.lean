import sympy.matrices.expressions.permutation
import sympy.Basic


@[main]
private lemma main
-- given
  (i i₀ j₀ : Fin n) :
-- imply
  (i.shiftRow i₀ j₀ : ℕ) =
    if (i : ℕ) = (j₀ : ℕ) then ↑i₀
    else if (j₀ : ℕ) < (i : ℕ) ∧ (i : ℕ) ≤ (i₀ : ℕ) then i.val - 1
    else if (i₀ : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (j₀ : ℕ) then ↑i + 1
    else i := by
-- proof
  simp only [Fin.shiftRow, Set.mem_Ioc, Set.mem_Ico]
  split_ifs <;> first
  | rfl
  | omega


-- created on 2026-09-12
