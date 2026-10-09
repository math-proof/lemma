import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Bool.OrOr.is.Or_Or |
| comm | Bool.Or_Or.is.OrOr |
-/
@[path, comm]
private lemma main :
-- imply
  (p ∨ q) ∨ r ↔ p ∨ q ∨ r :=
-- proof
  or_assoc


-- created on 2024-07-01
