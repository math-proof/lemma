import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : α)
  (s : List α):
-- imply
  x ∈ s ↔ ∃ i : Fin s.length, x = s[i] := by
-- proof
  rw [List.mem_iff_get]
  simp [Eq.comm]


-- created on 2025-06-14
