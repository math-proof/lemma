import Lemma.Bool.All.of.All.limits.subst.Neg
open Bool


@[path]
private lemma real
  {f : ℝ → Prop}
  {a b c : ℝ} :
-- imply
  (∀ x ∈ Set.Ioc a b, f x) ↔ ∀ x ∈ Set.Ico (c - b) (c - a), f (c - x) := by
-- proof
  refine ⟨All.of.All.limits.subst.Neg.real, fun h x hx => ?_⟩
  have h' := h (c - x) (by simp only [Set.mem_Ico, Set.mem_Ioc] at hx ⊢; constructor <;> linarith [hx.1, hx.2])
  rwa [sub_sub_cancel] at h'


-- created on 2018-12-20
