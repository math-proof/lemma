import Lemma.Basic


@[main]
private lemma main
  {p : (T : Sort u) → T → Prop}
  {a : α}
  {b : β}
-- given
  (h₀ : HEq a b)
  (h₁ : p α a) :
-- imply
  p β b :=
-- proof
  h₀.subst h₁


-- created on 2025-07-15
