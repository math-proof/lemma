import sympy.concrete.quantifier
import sympy.Basic


@[main]
private lemma setof
  {p f g : α → Prop}
-- given
  (h₀ : ∀ e | p x, f e)
  (h₁ : ∀ e | p x, g e) :
-- imply
  ∀ e | p x, f e ∧ g e := by
-- proof
  intro e h_e
  apply And.intro
  exact h₀ e h_e
  exact h₁ e h_e


@[main]
private lemma main
  {f g : α → Prop}
-- given
  (h₀ : ∀ e, f e)
  (h₁ : ∀ e, g e) :
-- imply
  ∀ e, f e ∧ g e := by
-- proof
  intro e
  apply And.intro
  exact h₀ e
  exact h₁ e


@[main]
private lemma given
  {f g : α → Prop}
-- given
  (h : ∀ e, f e ∧ g e) :
-- imply
  (∀ e, f e) ∧ ∀ e, g e := by
-- proof
  apply And.intro
  ·
    intro e
    apply (h e).1
  ·
    intro e
    apply (h e).2


-- created on 2018-09-29
