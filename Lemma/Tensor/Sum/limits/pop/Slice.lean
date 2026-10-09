import sympy.Basic


@[path]
private lemma main
  [Fintype β] [AddCommMonoid γ]
  {m : ℕ}
  {f : (Fin (m + 1) → β) → γ} :
-- imply
  ∑ v : Fin (m + 1) → β, f v = ∑ v : Fin m → β, ∑ b : β, f (Fin.snoc v b) := by
-- proof
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv ((Equiv.prodComm _ _).trans (Fin.snocEquiv fun _ => β)) _ _ (fun _ => rfl)).symm


-- created on 2020-12-20
