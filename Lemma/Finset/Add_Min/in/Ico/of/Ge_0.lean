import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x k : ℤ}
-- given
  (h₀ : k ≥ 0) :
-- imply
  k + min k (max (-k) x) ∈ Finset.Ico 0 (2 * k + 1) := by
-- proof
  rw [Finset.mem_Ico]
  refine ⟨?_, ?_⟩
  ·
    have hmin : -k ≤ min k (max (-k) x) := le_min (by omega) (le_max_left _ _)
    omega
  ·
    have hmax : min k (max (-k) x) ≤ k := min_le_left _ _
    omega


-- created on 2021-01-03
-- updated on 2026-10-26
