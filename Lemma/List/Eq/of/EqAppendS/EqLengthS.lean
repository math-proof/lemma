import Lemma.List.EqTakeAppend
import Lemma.List.EqDropAppend__Length
open List


@[main]
private lemma drop
  {a b a' b' : List α}
-- given
  (h₀ : a.length = b.length)
  (h₁ : a ++ a' = b ++ b') :
-- imply
  a' = b' := by
-- proof
  have ha := EqDropAppend__Length a a'
  have hb := EqDropAppend__Length b b'
  aesop


@[main]
private lemma main
  {a b a' b' : List α}
-- given
  (h₀ : a.length = b.length)
  (h₁ : a ++ a' = b ++ b') :
-- imply
  a = b := by
-- proof
  have ha := EqTakeAppend a a'
  have hb := EqTakeAppend b b'
  aesop


-- created on 2025-05-11
