import sympy.stats.stochastic_process_types
import Lemma.Matrix.EventuallyPositive.of.StochasticIrreducible.Aperiodic
import Mathlib.Data.Finset.Lattice.Fold


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
  {P : Matrix S S ℝ} [RowStochastic P] [StochasticIrreducible P] [Aperiodic P] :
-- imply
  ∃ N, 1 ≤ N ∧ DoeblinMinorization (P ^ N) := by
-- proof
  obtain ⟨n₀, hn₀⟩ := Matrix.EventuallyPositive.of.StochasticIrreducible.Aperiodic (P := P)
  let n₁ := n₀ + 1
  have hn₁ : ∀ i j, 0 < (P ^ n₁) i j := fun i j => hn₀ n₁ i j (by simp [n₁])
  have hne : (Finset.univ (α := S × S)).Nonempty := by simp
  let δij : S × S → ℝ := fun ij => (P ^ n₁) ij.1 ij.2
  let δ := Finset.inf' (Finset.univ (α := S × S)) hne δij
  have hδinf : ∀ ij, δ ≤ δij ij := fun ij =>
    Finset.inf'_le (f := δij) (by simp)
  have hδpos : 0 < δ := by
    obtain ⟨ij, -, hijinf⟩ := Finset.exists_mem_eq_inf' hne δij
    have := hn₁ ij.1 ij.2
    have : δ = δij ij := by simp [δ, hijinf]
    linarith
  have hδle1 : δ ≤ 1 := by
    obtain ⟨ij, -, hijinf⟩ := Finset.exists_mem_eq_inf' hne δij
    have hrow := RowStochastic.stochastic (P := P ^ n₁) ij.1
    calc
      _ = δij ij := by simp [δ, hijinf]
      _ ≤ ∑ k, (P ^ n₁) ij.1 k := by
        simp only [δij]
        have hmem : ij.2 ∈ (Finset.univ : Finset S) := by simp
        rw [← Finset.sum_erase_add _ _ hmem]
        exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => hrow.nonneg _)
      _ = 1 := hrow.rowsum
  refine ⟨n₁, by simp [n₁], ⟨?_⟩⟩
  refine ⟨δ / 2, uniform_distribution, by positivity, by linarith [hδle1], inferInstance, fun i j => ?_⟩
  have hν1 : uniform_distribution (S := S) j ≤ 1 := by
    simp [uniform_distribution]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_of_lt Fintype.card_pos)
  calc
    _ ≤ (δ / 2) * 1 := mul_le_mul_of_nonneg_left hν1 (by positivity)
    _ = δ / 2 := by ring
    _ ≤ δ := by linarith
    _ ≤ (P ^ n₁) i j := by simpa [δij] using hδinf (i, j)

-- created on 2026-09-22
-- updated on 2026-09-24
