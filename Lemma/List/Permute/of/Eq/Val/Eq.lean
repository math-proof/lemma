import stdlib.List


@[main]
private lemma main
  {s s' : List α}
  {i : Fin s.length}
  {i' : Fin s'.length}
  {d d' : ℤ}
-- given
  (h_s : s = s')
  (h_i : i.val = i'.val)
  (h_d : d = d') :
-- imply
  s.permute i d = s'.permute i' d' := by
-- proof
  subst h_s h_d
  grind


-- created on 2026-07-03
-- updated on 2026-07-04
