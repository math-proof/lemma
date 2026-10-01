import sympy.Basic


@[main]
private lemma main
  [Nonempty α]
  {f : α → Prop}
-- given
  (h : ∀ e, f e) :
-- imply
  ∃ e, f e :=
-- proof
  ⟨Classical.arbitrary α, h _⟩


-- created on 2026-09-27
