import sympy.sets.sets
import sympy.Basic


@[main]
private lemma swap1
  {n : ℕ}
  {x : Fin (n + 1) → ℤ}
  {i j : Fin (n + 1)} :
-- imply
  x (Equiv.swap 0 j i) = if i = j then x 0 else if i = 0 then x j else x i := by
-- proof
  rw [Equiv.swap_apply_def]
  split_ifs <;> simp_all


@[main]
private lemma swap1.helper
  {n : ℕ}
  {x : Fin (n + 1) → ℤ}
  {j : Fin (n + 1)} :
-- imply
  (fun i => x (Equiv.swap 0 j i)) = fun i => if i = j then x 0 else if i = 0 then x j else x i := by
-- proof
  funext i
  exact swap1


-- created on 2026-09-27
