import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  [Fintype α] [DecidableEq α] [CommMonoid β]
  {n i : ℕ}
  {f : (Fin (n - i + 1) → α) → β} :
-- imply
  ∏ x : Fin (n - i + 1) → α, f x = ∏ t : Fin (n - i) → α, ∏ a : α, f (Fin.snoc t a) := by
-- proof
  rw [← (Fin.snocEquiv (fun _ => α)).prod_comp, Fintype.prod_prod_type, Finset.prod_comm]
  rfl


-- created on 2023-11-18
