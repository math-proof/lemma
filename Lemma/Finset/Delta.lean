import sympy.sets.sets
import sympy.Basic


@[main]
private lemma concat
  {n : ℕ} :
-- imply
  (fun k : Fin (n + 1) => if (k : ℕ) = n then (1 : ℤ) else 0) = Fin.snoc (α := fun _ => ℤ) (0 : Fin n → ℤ) 1 := by
-- proof
  funext k
  cases k using Fin.lastCases with
  | last =>
    simp
  | cast i =>
    simp [i.isLt.ne]


-- created on 2026-09-27
