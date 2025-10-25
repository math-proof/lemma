import sympy.Basic


@[main]
private lemma main
  {f f' : α → α}
-- given
  (h_f : Function.Surjective f)
  (h : ∀ x, f' (f x) = x) :
-- imply
  ∀ x, f (f' x) = x := by
-- proof
  intro x
  let ⟨y, hy⟩ := h_f x
  rw [← hy, h y]


-- created on 2025-10-25
