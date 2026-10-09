import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {S : Set α}
  {p : α → Prop}
-- given
  (h : ∀ x ∈ S, p x) :
-- imply
  ∀ x ∈ S, p x ∧ S ≠ ∅ := by
-- proof
  exact fun x hx => ⟨h x hx, Set.nonempty_iff_ne_empty.mp ⟨x, hx⟩⟩


-- created on 2020-04-21
