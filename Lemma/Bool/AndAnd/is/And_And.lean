import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Bool.AndAnd.is.And_And |
| comm | Bool.And_And.is.AndAnd |
-/
@[path, comm]
private lemma main :
-- imply
  (p ∧ q) ∧ r ↔ p ∧ q ∧ r :=
-- proof
  and_assoc


-- created on 2024-07-01
