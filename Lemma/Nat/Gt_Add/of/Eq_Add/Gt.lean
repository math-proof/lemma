import sympy.Basic


@[main]
private lemma main
  [Add α]
  [LT α]
  [AddLeftStrictMono α]
  [AddLeftReflectLT α]
  {a b b' c : α}
-- given
  (h₀ : c = a + b)
  (h₁ : b > b') :
-- imply
  c > a + b' := by
-- proof
  subst h₀
  simpa


-- created on 2025-03-20
