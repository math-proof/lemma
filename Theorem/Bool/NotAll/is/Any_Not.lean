module

public import Theorem.Bool.Any.is.NotAll_Not

public section

open Bool


/--
| attributes | lemma |
| :---: | :---: |
| path | Bool.NotAll.is.Any_Not |
| comm | Bool.Any_Not.is.NotAll |
-/
@[comm]
public theorem Bool.NotAll.is.Any_Not
-- given
  (p : α → Prop) :
-- imply
  (¬∀ x : α, p x) ↔ ∃ x : α, ¬p x := by
-- proof
  rw [Any.is.NotAll_Not]
  simp


-- created on 2024-07-01
