import sympy.Basic


@[path]
private lemma main
  {f : ℤ → Prop}
  {a b c : ℤ}
-- given
  (h : ∃ n ∈ Set.Ico a b, f n) :
-- imply
  ∃ n ∈ Set.Ico (c + 1 - b) (c + 1 - a), f (c - n) := by
-- proof
  obtain ⟨n, hn, hf⟩ := h
  refine ⟨c - n, ?_, by rwa [sub_sub_cancel]⟩
  simp only [Set.mem_Ico] at hn ⊢
  omega


@[path]
private lemma real
  {f : ℝ → Prop}
  {a b c : ℝ}
-- given
  (h : ∃ x ∈ Set.Ioc a b, f x) :
-- imply
  ∃ x ∈ Set.Ico (c - b) (c - a), f (c - x) := by
-- proof
  obtain ⟨x, hx, hf⟩ := h
  refine ⟨c - x, ?_, by rwa [sub_sub_cancel]⟩
  simp only [Set.mem_Ico, Set.mem_Ioc] at hx ⊢
  constructor <;> linarith [hx.1, hx.2]


-- created on 2019-02-18
