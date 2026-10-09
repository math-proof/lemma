import sympy.Basic


@[path]
private lemma main
  [Add α]
  {m n : ℕ}
  {a : Fin m → α}
  {b : Fin n → α}
  {c : α} :
-- imply
  (fun i => Fin.append a b i + c) = Fin.append (fun i => a i + c) (fun i => b i + c) := by
-- proof
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  ·
    simp
  ·
    simp


-- created on 2022-01-14
