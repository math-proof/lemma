import sympy.Basic


@[main]
private lemma main
  {bool : Bool} :
-- imply
  match bool with
  | true => True
  | false => True ↔ True := by
-- proof
  cases bool <;> simp


-- created on 2024-07-01
