import Lemma.Logic.Imp.is.OrNot
import Lemma.Logic.NotAnd.is.OrNotS
import Lemma.Logic.OrOr.is.Or_Or
open Logic


@[main]
private lemma main :
-- imply
  p → q → r ↔ p ∧ q → r := by
-- proof
  repeat rw [Imp.is.OrNot]
  rw [NotAnd.is.OrNotS]
  rw [OrOr.is.Or_Or]


-- created on 2024-07-01
