import Lemma.Bool.EqIteS.of.Imp_Eq
open Bool


@[main]
private lemma main
  [Decidable p]
  [Decidable q]
  {f : α → α}
  {x a b c L : α}
-- given
  (h₀ : p → x = a)
  (h₁ : L = if q then
    b
  else if p then
    f x
  else
    c) :
-- imply
  L = if q then
    b
  else if p then
    f a
  else
    c := by
-- proof
  rwa [EqIteS.of.Imp_Eq h₀] at h₁


-- created on 2025-04-19
