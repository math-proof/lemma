import sympy.sets.sets
import sympy.Basic


@[main]
private lemma limits.subst.offset.given
  {f : ℤ → Prop}
  {a b d : ℤ}
-- given
  (h : ∃ n ∈ Set.Ico (a - d) (b - d), f (n + d)) :
-- imply
  ∃ n ∈ Set.Ico a b, f n := by
-- proof
  obtain ⟨n, hn, hf⟩ := h
  refine ⟨n + d, ?_, hf⟩
  simp only [Set.mem_Ico] at hn ⊢
  omega


-- created on 2026-09-27
