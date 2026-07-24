import sympy.Basic


@[main]
private lemma main
  {a b : List α}
  {i : ℕ}
-- given
  (h_i : a.length > i)
  (h_eq : a.length = b.length)
  (h : a[i] = b[i]) :
-- imply
  a[i]? = b[i]? := by
-- proof
  simp [h_i]
  have h_i : i < b.length := by
    rwa [← h_eq]
  simpa [h_i]


-- created on 2025-07-05
