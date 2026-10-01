import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : Fin n → α}
  {S : Set α} :
-- imply
  x ∈ Set.univ.pi (fun _ => S) ↔ ∀ k, x k ∈ S := by
-- proof
  simp


-- created on 2026-09-27
