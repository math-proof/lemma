import sympy.Basic


@[path]
private lemma main
  [One α]
  {p q m : ℕ} :
-- imply
  (fun (_ : Fin (p + q)) (_ : Fin m) => (1 : α)) = Fin.append (fun (_ : Fin p) (_ : Fin m) => (1 : α)) (fun (_ : Fin q) (_ : Fin m) => (1 : α)) := by
-- proof
  funext i
  exact Fin.addCases (fun i => by simp) (fun i => by simp) i


-- created on 2021-10-07
