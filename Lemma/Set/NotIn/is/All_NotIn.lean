import sympy.sets.sets
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.NotIn.is.All_NotIn |
| mpr | Set.NotIn.of.All_NotIn |
-/
@[main, mpr]
private lemma main
  {n : ℕ}
  {x : α}
  {A : ℕ → Set α} :
-- imply
  x ∉ ⋃ k ∈ Finset.range n, A k ↔ ∀ k ∈ Finset.range n, x ∉ A k := by
-- proof
  constructor
  ·
    intro h
    simp only [Set.mem_iUnion, not_exists] at h
    exact h
  ·
    intro h hx
    obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp hx
    exact h k hk hxk


-- created on 2026-10-07
