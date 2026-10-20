import Mathlib.Logic.Equiv.Defs
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  (x : Fin (n + 1) → α)
  (j : Fin (n + 1)) :
-- imply
  (fun i => x (Equiv.swap 0 j i))
    = fun i => if i = j then x 0 else if i = 0 then x j else x i := by
-- proof
  funext i
  if hij : i = j then
    subst hij
    simp [Equiv.swap_apply_right]
  else if hi : i = 0 then
    subst hi
    simp [Equiv.swap_apply_left, hij]
  else
    rw [Equiv.swap_apply_of_ne_of_ne hi hij]
    simp [hij, hi]


-- created on 2020-09-12
-- updated on 2026-10-17
