import Lemma.Multiset.AntitoneOnFunPowNesymm
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma symmetric_mean_inequality
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h : ∀ i, x i > 0) :
-- imply
  ∀ k ∈ Finset.Ico 1 n,
    (((Finset.range n).val.map x).esymm k / n.choose k) ^ (1 / (k : ℝ)) ≥
      (((Finset.range n).val.map x).esymm (k + 1) / n.choose (k + 1)) ^ (1 / ((k : ℝ) + 1)) := by
-- proof
  intro k hk
  rw [Finset.mem_Ico] at hk
  have A := Multiset.AntitoneOnFunPowNesymm (s := (Finset.range n).val.map x) (fun y hy => by
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hy
    exact (h i).le)
  have B := A (show 1 ≤ k from hk.1) (show 1 ≤ k + 1 by omega) (Nat.le_succ k)
  simp only [nesymm, Multiset.card_map, Finset.card_val, Finset.card_range, Nat.cast_add, Nat.cast_one] at B
  rw [ge_iff_le, one_div, one_div]
  exact B


-- created on 2020-11-05
