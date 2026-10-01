import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [Fintype α] [DecidableEq α] [CommMonoid β]
  {n i : ℕ}
  {f : (Fin (n - i + 1) → α) → β} :
-- imply
  ∏ x : Fin (n - i + 1) → α, f x = ∏ a : α, ∏ t : Fin (n - i) → α, f (Fin.cons a t) := by
-- proof
  rw [← (Fin.consEquiv (fun _ => α)).prod_comp, Fintype.prod_prod_type]
  rfl


-- created on 2026-09-27
