import Lemma.List.EqDropAppend
import Lemma.List.EqTakeAppend
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
  have ha := EqDropAppend a a'
  have hb := EqDropAppend b b'
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
-- updated on 2026-07-20
