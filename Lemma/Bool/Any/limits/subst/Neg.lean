import Lemma.Bool.Any.of.Any.limits.subst.Neg
open Bool


@[main]
private lemma main
  {f : ℤ → Prop}
  {a b c : ℤ} :
-- imply
  (∃ i ∈ Set.Ico a b, f i) ↔ ∃ i ∈ Set.Ico (c + 1 - b) (c + 1 - a), f (c - i) := by
-- proof
  refine ⟨Any.of.Any.limits.subst.Neg, ?_⟩
  rintro ⟨i, hi, hf⟩
  refine ⟨c - i, ?_, hf⟩
  simp only [Set.mem_Ico] at hi ⊢
  omega


@[main]
private lemma real
  {f : ℝ → Prop}
  {a b c : ℝ} :
-- imply
  (∃ x ∈ Set.Ico a b, f x) ↔ ∃ x ∈ Set.Ioc (c - b) (c - a), f (c - x) := by
-- proof
  constructor
  ·
    rintro ⟨x, hx, hf⟩
    refine ⟨c - x, ?_, by rwa [sub_sub_cancel]⟩
    simp only [Set.mem_Ico, Set.mem_Ioc] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]
  ·
    rintro ⟨x, hx, hf⟩
    refine ⟨c - x, ?_, hf⟩
    simp only [Set.mem_Ico, Set.mem_Ioc] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]


-- created on 2019-02-20
