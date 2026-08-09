import sympy.vector.Basic


@[main]
private lemma main
-- given
  (h_start : start = start')
  (h_stop : stop = stop')
  (h_step : step = step')
  (h_n : n = n')
  (h_i' : i < (⟨start', stop', step'⟩ : Slice).length n')
  (h_i : i < (⟨start, stop, step⟩ : Slice).length n) :
-- imply
  (List.Vector.indices ⟨start, stop, step⟩ n)[i].val = (List.Vector.indices ⟨start', stop', step'⟩ n')[i].val := by
-- proof
  subst h_start h_stop h_step h_n
  grind


-- created on 2025-05-27
-- updated on 2025-05-28
