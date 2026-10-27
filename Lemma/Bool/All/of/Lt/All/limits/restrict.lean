import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b c : ℝ}
  {p : ℝ → Prop}
-- given
  (hlt : c < b)
  (h : ∀ x ∈ Set.Ico a b, p x) :
-- imply
  ∀ x ∈ Set.Ico a c, p x := by
-- proof
  intro x hx
  apply h x
  simp only [Set.mem_Ico] at hx ⊢
  constructor
  ·
    apply hx.1
  ·
    apply lt_trans hx.2 hlt


-- created on 2019-12-12
