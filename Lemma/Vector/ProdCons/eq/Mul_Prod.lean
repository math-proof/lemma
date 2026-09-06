import sympy.vector.vector


@[main]
private lemma main
  [Mul α] [One α]
-- given
  (a : α)
  (l : List.Vector α n) :
-- imply
  (a ::ᵥ l).prod = a * l.prod := by
-- proof
  obtain ⟨l, hl⟩ := l
  unfold List.Vector.prod
  simp


-- created on 2026-09-06
