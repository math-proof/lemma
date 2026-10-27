import Theorem.Logic.SEq
import Initialize.Tactic.Attr.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Bool.SEq.is.Eq |
| comm | Bool.Eq.is.SEq |
| mp | Bool.Eq.of.SEq |
| mpr | Bool.SEq.of.Eq |
-/
@[path, comm, mp, mpr]
private lemma main
  {Vector : α → Sort v}
-- given
  (a b : Vector n) :
-- imply
  a ≃ b ↔ a = b := by
-- proof
  constructor <;>
    intro h
  .
    simp [SEq] at h
    assumption
  .
    rw [h]


-- created on 2025-07-25
