import Lemma.Basic


@[main]
private lemma main
  {a : List α}
-- given
  (h : a.length > 0) :
-- imply
  a.take 1 = [a[0]] := by
-- proof
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_length_pos h
    -- Both sides reduce definitionally to `[x]`
  rfl


-- created on 2025-06-17
