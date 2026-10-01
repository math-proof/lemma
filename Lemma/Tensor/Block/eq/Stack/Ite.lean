import sympy.Basic


@[main]
private lemma main
  {m n : ℕ}
  {A : Fin m → α}
  {B : Fin n → α} :
-- imply
  Fin.append A B = fun i : Fin (m + n) => if h : (i : ℕ) < m then A ⟨i, h⟩ else B ⟨i - m, by omega⟩ := by
-- proof
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  ·
    simp
  ·
    simp


-- created on 2021-12-20
