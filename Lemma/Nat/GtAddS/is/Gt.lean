import sympy.Basic


@[path]
private lemma main
  [Add α]
  [LT α]
  [AddRightStrictMono α]
  [AddRightReflectLT α]
-- given
  (a b c : α) :
-- imply
  b + a > c + a ↔ b > c :=
-- proof
  ⟨lt_of_add_lt_add_right, (add_lt_add_left · a)⟩


-- created on 2018-05-19
