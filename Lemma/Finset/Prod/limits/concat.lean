import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import sympy.Basic


@[path]
private lemma main
  [Fintype β] [CommMonoid γ]
  {m : ℕ}
  {f : (Fin (m + 1) → β) → γ} :
-- imply
  ∏ a : β, ∏ v : Fin m → β, f (Fin.cons a v) = ∏ w : Fin (m + 1) → β, f w := by
-- proof
  rw [← Fintype.prod_prod_type']
  apply Fintype.prod_equiv (Fin.consEquiv (fun _ => β))
  intro w
  rfl


-- created on 2023-11-18
-- updated on 2026-10-17
