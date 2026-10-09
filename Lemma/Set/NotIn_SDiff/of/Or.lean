import sympy.Basic


@[path]
private lemma main
  {e : α}
  {U A : Set α}
-- given
  (h : e ∉ U ∨ e ∈ A) :
-- imply
  e ∉ U \ A :=
-- proof
  fun ⟨h₁, h₂⟩ => h.elim (· h₁) h₂


-- created on 2018-02-25
