import sympy.Basic


@[main]
private lemma main
  {S : Set α}
  {f : β → α}
  {x : β}
-- given
  (h : f x ∈ S) :
-- imply
  ∃ w ∈ S, w = f x :=
-- proof
  ⟨f x, h, rfl⟩


-- created on 2026-09-26
