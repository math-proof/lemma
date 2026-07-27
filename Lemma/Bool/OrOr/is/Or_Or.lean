import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.OrOr.is.Or_Or |
| comm | Bool.Or_Or.is.OrOr |
-/
@[main, comm]
private lemma main :
-- imply
  (p ∨ q) ∨ r ↔ p ∨ q ∨ r :=
-- proof
  or_assoc


-- created on 2024-07-01
