import sympy.Basic
import sympy.vector.vector


@[main]
private lemma main
  {v : List.Vector α 1}
-- given
  (h : v = ⟨[v₀], by simp⟩) :
-- imply
  v.head = v₀ := by
-- proof
  subst h
  simp [List.Vector.head]


-- created on 2026-04-24
