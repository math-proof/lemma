import Lemma.Algebra.EqTakeAppend__Length
import Lemma.Algebra.EqDropAppend__Length
open Algebra


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
  have ha := EqTakeAppend__Length a a'
  have hb := EqTakeAppend__Length b b'
  aesop


-- created on 2025-05-11
