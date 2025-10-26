import Lemma.Nat.Ne.of.Lt
import Lemma.Bool.Eq.is.False.of.Ne
open Bool Nat


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : a < b) :
-- imply
  a = b ↔ False := by
-- proof
  have := Ne.of.Lt h
  apply Eq.is.False.of.Ne this


-- created on 2025-03-27
-- updated on 2025-03-29
