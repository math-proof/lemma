import sympy.functions.combinatorial.numbers
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma s1
  {n k : ℕ}
-- given
  (h₀ : 0 < k)
  (h₁ : k ≤ n) :
-- imply
  Stirling.conditionset n k ≠ ∅ := by
-- proof
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  apply Set.nonempty_iff_ne_empty.mp
  refine ⟨Fin.snoc (α := fun _ => Finset ℕ) (fun i : Fin m => {(i : ℕ)}) (Finset.Ico m n), ?_, ?_, ?_⟩
  · ext y
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Fin.exists_fin_succ', Fin.snoc_castSucc, Fin.snoc_last,
      Finset.mem_singleton, Finset.mem_Ico, Finset.mem_range]
    constructor
    · rintro (⟨i, rfl⟩ | h)
      · have := i.isLt
        omega
      · exact h.2
    · intro hy
      by_cases hym : y < m
      · exact Or.inl ⟨⟨y, hym⟩, rfl⟩
      · exact Or.inr ⟨by omega, hy⟩
  · rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Finset.card_singleton, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one, Nat.card_Ico]
    omega
  · intro i
    cases i using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last, Nat.card_Ico]
      omega
    | cast i =>
      rw [Fin.snoc_castSucc, Finset.card_singleton]
      exact Nat.one_pos


-- created on 2020-11-08
