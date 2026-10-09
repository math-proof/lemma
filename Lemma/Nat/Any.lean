import sympy.sets.sets
import sympy.Basic


@[path]
private lemma limits.subst.offset
  {f : ℤ → Prop}
  {a b d : ℤ} :
-- imply
  (∃ n ∈ Set.Ico a b, f n) ↔ ∃ n ∈ Set.Ico (a - d) (b - d), f (n + d) := by
-- proof
  constructor
  · rintro ⟨n, hn, hf⟩
    refine ⟨n - d, ?_, by rwa [sub_add_cancel]⟩
    simp only [Set.mem_Ico] at hn ⊢
    omega
  · rintro ⟨n, hn, hf⟩
    refine ⟨n + d, ?_, hf⟩
    simp only [Set.mem_Ico] at hn ⊢
    omega


-- created on 2026-09-27
