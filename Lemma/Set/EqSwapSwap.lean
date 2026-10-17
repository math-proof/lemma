import sympy.Basic


@[path]
private lemma main
  [DecidableEq ι]
  {i j : ι}
  {x : ι → α} :
-- imply
  (fun k =>
    let y := fun k => if k = i then x j else if k = j then x i else x k
    if k = i then y j else if k = j then y i else y k) = x := by
-- proof
  funext k
  grind


-- created on 2026-10-11
-- updated on 2026-10-17
