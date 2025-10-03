import sympy.vector.vector
import sympy.Basic


@[main]
private lemma main
  {f g : α → β}
-- given
  (h : ∀ a : α, f a = g a)
  (L : List.Vector α n) :
-- imply
  L.map f = L.map g := by
-- proof
  have h_eq : f = g := by
    funext i
    apply h
  rw [h_eq]


-- created on 2025-05-23
