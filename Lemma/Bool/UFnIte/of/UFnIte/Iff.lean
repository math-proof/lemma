import Lemma.Bool.Ite.of.Iff
open Bool


@[main]
private lemma main
  [Decidable p]
  [Decidable q]
  {R : β → Prop}
  {f : α → β}
  {a b : α}
-- given
  (h₀ : p ↔ q)
  (h₁ : R (if p then
    f a
  else
    f b)) :
-- imply
  R (if q then
    f a
  else
    f b) :=
-- proof
  (Ite.of.Iff h₀) ▸ h₁


-- created on 2018-07-20
