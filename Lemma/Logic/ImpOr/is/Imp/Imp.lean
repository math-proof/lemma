import Lemma.Logic.Imp.is.OrNot
import Lemma.Logic.And_Or.is.OrAndS
import Lemma.Logic.AndOr.is.OrAndS
import Lemma.Logic.OrOr.is.Or_Or
import Lemma.Logic.OrAnd.is.AndOrS
import Lemma.Logic.IffAndOr
open Logic


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
