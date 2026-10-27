import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [DecidableEq ι]
  {i j : ι}
  {x y : ι → α}
-- given
  (h₀ : x = y) :
-- imply
  (fun k => if k = i then x j else if k = j then x i else x k) =
    fun k => if k = i then y j else if k = j then y i else y k := by
-- proof
  rw [h₀]


-- created on 2021-03-30
-- updated on 2026-10-26
