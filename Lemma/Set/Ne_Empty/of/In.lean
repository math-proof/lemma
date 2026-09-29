import sympy.Basic


@[main]
private lemma main
  {x : α}
  {S : Set α}
-- given
  (h : x ∈ S) :
-- imply
  S ≠ ∅ :=
-- proof
  Set.nonempty_iff_ne_empty.mp ⟨x, h⟩


-- created on 2026-09-27
