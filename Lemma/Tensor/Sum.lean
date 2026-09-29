import sympy.Basic


@[main]
private lemma limits.concat
  [Fintype β] [AddCommMonoid γ]
  {m : ℕ}
  {f : (Fin (m + 1) → β) → γ} :
-- imply
  ∑ a : β, ∑ v : Fin m → β, f (Fin.cons a v) = ∑ w : Fin (m + 1) → β, f w := by
-- proof
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.consEquiv (fun _ => β)) _ _ (fun _ => rfl)


-- created on 2026-09-27
