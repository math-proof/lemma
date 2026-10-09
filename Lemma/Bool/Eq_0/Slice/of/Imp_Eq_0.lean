import sympy.Basic


@[path]
private lemma main
  [Zero α]
  {i : ℕ}
  {L : ℕ → ℕ → α}
-- given
  (h : ∀ j, j > i → L i j = 0) :
-- imply
  (fun t => L i (i + 1 + t)) = 0 :=
-- proof
  funext fun t => h _ (by omega)


-- created on 2023-06-23
