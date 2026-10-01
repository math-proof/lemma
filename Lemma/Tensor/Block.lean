import sympy.Basic


@[main]
private lemma split
  {k l n₀ n₁ : ℕ}
  {A : Fin (k + l) → Fin n₀ → ℝ}
  {B : Fin (k + l) → Fin n₁ → ℝ} :
-- imply
  (fun i => Fin.append (A i) (B i)) =
    Fin.append (fun i => Fin.append (A (Fin.castAdd l i)) (B (Fin.castAdd l i))) (fun i => Fin.append (A (Fin.natAdd k i)) (B (Fin.natAdd k i))) := by
-- proof
  funext i
  exact Fin.addCases (fun i => by simp) (fun i => by simp) i


-- created on 2026-09-27
