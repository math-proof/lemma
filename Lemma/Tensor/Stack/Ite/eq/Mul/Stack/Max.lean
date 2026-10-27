import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ} :
-- imply
  ∀ i j : Fin n,
    (if i = j then (0 : ℝ) else (min i.1 j.1 : ℝ)) =
      (1 - if i = j then 1 else 0) * (min i.1 j.1 : ℝ) ∧
    (if i = j then (0 : ℝ) else (max i.1 j.1 : ℝ)) =
      (1 - if i = j then 1 else 0) * (max i.1 j.1 : ℝ) := by
-- proof
  intro i j
  constructor
  ·
    if h : i = j then
      simp [h]
    else
      simp [h]
  ·
    if h : i = j then
      simp [h]
    else
      simp [h]


-- created on 2019-10-17
-- updated on 2026-10-26
