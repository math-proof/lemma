import Lemma.List.Eq.of.EqAppendS.EqLengthS
import Lemma.List.EqTakeAppend
open List


@[main]
private lemma drop
  {a b a' b' : List α}
-- given
  (h₁ : a ++ a' = b ++ b')
  (h₀ : a'.length = b'.length) :
-- imply
  a' = b' := by
-- proof
  apply Eq.of.EqAppendS.EqLengthS.drop _ h₁
  have := congrArg List.length h₁
  simp only [length_append] at this
  omega


@[main]
private lemma main
  {a b a' b' : List α}
-- given
  (h₁ : a ++ a' = b ++ b')
  (h₀ : a'.length = b'.length) :
-- imply
  a = b := by
-- proof
  apply Eq.of.EqAppendS.EqLengthS _ h₁
  have := congrArg List.length h₁
  simp only [length_append] at this
  omega


-- created on 2026-07-20
