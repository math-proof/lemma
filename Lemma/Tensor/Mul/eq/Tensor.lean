import sympy.Basic


@[main]
private lemma main
  [Mul α]
  {a b c d x : α} :
-- imply
  (fun i => (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d finZeroElim))) : Fin 4 → α) i * x) =
    (Fin.cons (a * x) (Fin.cons (b * x) (Fin.cons (c * x) (Fin.cons (d * x) finZeroElim))) : Fin 4 → α) := by
-- proof
  funext i
  fin_cases i <;> rfl


-- created on 2022-07-08
