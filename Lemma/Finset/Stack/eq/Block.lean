import sympy.Basic


@[main]
private lemma split
  {p q n : ℕ}
  {f : ℕ → ℕ → α} :
-- imply
  (fun (i : Fin (p + q)) (j : Fin n) => f i j) = Fin.append (fun (i : Fin p) (j : Fin n) => f i j) (fun (i : Fin q) (j : Fin n) => f (p + i) j) := by
-- proof
  funext i
  exact Fin.addCases (fun i => by simp) (fun i => by simp) i


-- created on 2026-09-27
