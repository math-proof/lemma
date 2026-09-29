import Lemma.Nat.All.of.All
open Nat


@[main]
private lemma limits.subst.offset
  {f : ℤ → Prop}
  {a b d : ℤ} :
-- imply
  (∀ n ∈ Set.Ico a b, f n) ↔ ∀ n ∈ Set.Ico (a - d) (b - d), f (n + d) := by
-- proof
  refine ⟨fun h n hn => h (n + d) ?_, All.of.All.limits.subst.offset.given⟩
  simp only [Set.mem_Ico] at hn ⊢
  omega


-- created on 2026-09-27
