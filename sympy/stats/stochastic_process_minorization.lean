import sympy.stats.stochastic_process_types
import Lemma.Set.Any_All_In.of.ClosedUnderAdd.FiniteGCDOne
import Lemma.Matrix.Ge_Mul.of.PowAdd
import Lemma.Matrix.ReturnTimes.ClosedUnderAdd
open Finset Matrix StochasticMatrix
open scoped Matrix BigOperators

namespace StochasticMatrix

universe u
variable {S : Type u} [Fintype S] [DecidableEq S]

theorem eventually_positive [Nonempty S] (P : Matrix S S ℝ) [RowStochastic P]
    [StochasticIrreducible P] [Aperiodic P] :
    ∃ N, ∀ n i j, N ≤ n → 0 < (P ^ n) i j := by
  let h_exists_ni := fun i =>
    (Set.Any_All_In.of.ClosedUnderAdd.FiniteGCDOne
      (A := return_times P i))
  let ni := fun i => (h_exists_ni i).choose
  have hdiag : ∃ N, ∀ n i, N ≤ n → 0 < (P ^ n) i i := by
    have hne : (Finset.univ (α := S)).Nonempty := by simp
    refine ⟨?N, ?hN⟩
    case N => exact Finset.sup' (Finset.univ (α := S)) hne ni
    case hN =>
      intro n i hnge
      have hni : ni i ≤ n := by
        have : i ∈ Finset.univ (α := S) := by simp
        have := Finset.le_sup' ni this
        linarith
      have := (h_exists_ni i).choose_spec n hni
      simp [return_times] at this
      exact this.2
  obtain ⟨n₀, hn₀⟩ := hdiag
  let h_exists_nij := fun ij : S × S =>
    (inferInstance : StochasticIrreducible P).irreducible ij.1 ij.2
  let nij := fun ij => (h_exists_nij ij).choose
  have hne2 : (Finset.univ (α := S × S)).Nonempty := by simp
  let n₁ := Finset.sup' (Finset.univ (α := S × S)) hne2 nij
  refine ⟨?N, ?hN⟩
  case N => exact n₀ + n₁
  case hN =>
    intro n i j hnge
    let ij := nij (i, j)
    have hij_le : ij ≤ n₁ := by
      have : (i, j) ∈ Finset.univ (α := S × S) := by simp
      have := Finset.le_sup' nij this
      linarith
    have hnijn : ij ≤ n := by linarith
    have hn : n₀ ≤ n - ij := by
      rw [Nat.le_sub_iff_add_le hnijn]
      linarith
    have hPnij : 0 < (P ^ ij) i j := (h_exists_nij (i, j)).choose_spec
    have hPn₀ : 0 < (P ^ (n - ij)) j j := hn₀ (n - ij) j hn
    calc
      0
    _ < (P ^ ij) i j * (P ^ (n - ij)) j j := mul_pos hPnij hPn₀
    _ ≤ (P ^ n) i j := by
      have hineq := Matrix.Ge_Mul.of.PowAdd P ij (n - ij) i j j
      have : ij + (n - ij) = n := Nat.add_sub_of_le hnijn
      rw [this] at hineq
      exact hineq.le

theorem smat_minorizable_with_large_pow [Nonempty S] (P : Matrix S S ℝ)
    [RowStochastic P] [StochasticIrreducible P] [Aperiodic P] :
    ∃ N, 1 ≤ N ∧ DoeblinMinorization (P ^ N) := by
  obtain ⟨n₀, hn₀⟩ := eventually_positive P
  let n₁ := n₀ + 1
  have hn₁ : ∀ i j, 0 < (P ^ n₁) i j := fun i j => hn₀ n₁ i j (by simp [n₁])
  have hne : (Finset.univ (α := S × S)).Nonempty := by simp
  let δij : S × S → ℝ := fun ij => (P ^ n₁) ij.1 ij.2
  let δ := Finset.inf' (Finset.univ (α := S × S)) hne δij
  have hδinf : ∀ ij, δ ≤ δij ij := fun ij =>
    Finset.inf'_le (f := δij) (by simp)
  have hδpos : 0 < δ := by
    obtain ⟨ij, -, hijinf⟩ := exists_mem_eq_inf' hne δij
    have := hn₁ ij.1 ij.2
    have : δ = δij ij := by simp [δ, hijinf]
    linarith
  have hδle1 : δ ≤ 1 := by
    obtain ⟨ij, -, hijinf⟩ := exists_mem_eq_inf' hne δij
    have hδdef : δ = δij ij := by simp [δ, hijinf]
    have hrow := RowStochastic.stochastic (P := P ^ n₁) ij.1
    have hle : δij ij ≤ ∑ k, (P ^ n₁) ij.1 k := by
      simp only [δij]
      have hmem : ij.2 ∈ (Finset.univ : Finset S) := by simp
      rw [← Finset.sum_erase_add _ _ hmem]
      exact le_add_of_nonneg_left (sum_nonneg fun _ _ => hrow.nonneg _)
    calc
        δ
      _ = δij ij := hδdef
      _ ≤ ∑ k, (P ^ n₁) ij.1 k := hle
      _ = 1 := hrow.rowsum
  refine ⟨n₁, by simp [n₁],
    ⟨δ / 2, uniform_distribution, ?hεpos, ?hεlt1,
      uniform_distribution_stochastic, ?hP⟩⟩
  · positivity
  · linarith [hδle1]
  · intro i j
    have hδ : δ ≤ (P ^ n₁) i j := by simpa [δij] using hδinf (i, j)
    have hν1 : uniform_distribution (S := S) j ≤ 1 := by
      simp [uniform_distribution]
      exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_of_lt Fintype.card_pos)
    have hhalf_nonneg : 0 ≤ δ / 2 := by positivity
    calc
        (δ / 2) * uniform_distribution j
      _ ≤ (δ / 2) * 1 := mul_le_mul_of_nonneg_left hν1 hhalf_nonneg
      _ = δ / 2 := by ring
      _ ≤ δ := by linarith
      _ ≤ (P ^ n₁) i j := hδ

end StochasticMatrix
