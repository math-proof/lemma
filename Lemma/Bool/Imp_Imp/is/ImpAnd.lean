import Lemma.Bool.Imp.is.OrNot
import Lemma.Bool.NotAnd.is.OrNotS
import Lemma.Bool.OrOr.is.Or_Or
open Bool


@[main]
private lemma main :
-- imply
  p → q → r ↔ p ∧ q → r := by
-- proof
  repeat rw [Imp.is.OrNot]
  rw [NotAnd.is.OrNotS]
  rw [OrOr.is.Or_Or]


-- created on 2024-07-01
