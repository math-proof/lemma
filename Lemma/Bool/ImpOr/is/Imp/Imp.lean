import Lemma.Bool.Imp.is.OrNot
import Lemma.Bool.And_Or.is.OrAndS
import Lemma.Bool.AndOr.is.OrAndS
import Lemma.Bool.OrOr.is.Or_Or
import Lemma.Bool.OrAnd.is.AndOrS
import Lemma.Bool.IffAndOr
open Bool


@[main]
private lemma main :
-- imply
  (p ∨ q) → r ↔ (p → r) ∧ (q → r)  := by
-- proof
  repeat rw [Imp.is.OrNot]
  rw [And_Or.is.OrAndS]
  simp
  repeat rw [AndOr.is.OrAndS]
  simp
  rw [OrOr.is.Or_Or]
  rw [OrAnd.is.AndOrS (q := r)]
  simp [OrAndS.is.AndOr.apart (p := r)]
  rw [Or_Or.is.OrOr]
  simp [IffAndOr true]


-- created on 2024-07-01
