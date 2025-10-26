import Lemma.Bool.BFnIteS.eq.IteAnd
open Bool


@[main]
private lemma main
  [Decidable p]
  [Decidable q]
  {f : α → α → α}
  {a a' b b' : α}
-- given
  (h : ∀ a b, f a b = f b a) :
-- imply
  f (if p then
    a
  else
    a') (if q then
    b
  else
    b') = if p ∧ q then
    f a b
  else if p then
    f a b'
  else if q then
    f a' b
  else
    f a' b' := by
-- proof
  rw [h]
  rw [BFnIteS.eq.IteAnd (f := f)]
  simp [And.comm (a := q)]
  rw [h]
  rw [h b' a]
  rw [h b a']
  rw [h b' a']


-- created on 2025-04-28
