import sympy.stats.stochastic_process_types
import Lemma.Set.Any_All_In.of.ClosedUnderAdd.FiniteGCDOne
import Lemma.Matrix.GetPow_Add.ge.MulGetSPow
import Lemma.Matrix.ReturnTimes.ClosedUnderAdd


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
  {P : Matrix S S ℝ} [RowStochastic P]
-- given
  (hS : StochasticIrreducible P)
  (hA : Aperiodic P) :
-- imply
  ∃ N, ∀ n i j, N ≤ n → 0 < (P ^ n) i j := by
-- proof
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
  let h_exists_nij := fun ij : S × S => hS.irreducible ij.1 ij.2
  let nij := fun ij => (h_exists_nij ij).choose
  have hne2 : (Finset.univ (α := S × S)).Nonempty := by simp
  let n₁ := Finset.sup' (Finset.univ (α := S × S)) hne2 nij
  refine ⟨?N, ?hN⟩
  case N => exact n₀ + n₁
  case hN =>
    intro n i j hnge
    set ij := nij (i, j) with hij_def
    have hij_le : ij ≤ n₁ := by
      rw [hij_def]
      have : (i, j) ∈ Finset.univ (α := S × S) := by simp
      have := Finset.le_sup' nij this
      linarith
    have hnijn : ij ≤ n := by omega
    have hn : n₀ ≤ n - ij := by
      rw [Nat.le_sub_iff_add_le hnijn]
      omega
    have hPnij : 0 < (P ^ ij) i j := by
      rw [hij_def]
      exact (h_exists_nij (i, j)).choose_spec
    have hPn₀ : 0 < (P ^ (n - ij)) j j := hn₀ (n - ij) j hn
    calc
      0
      _ < (P ^ ij) i j * (P ^ (n - ij)) j j := mul_pos hPnij hPn₀
      _ ≤ (P ^ n) i j := by
        have hineq := @Matrix.GetPow_Add.ge.MulGetSPow _ _ _ P _ ij (n - ij) i j j
        have : ij + (n - ij) = n := Nat.add_sub_of_le hnijn
        rwa [this] at hineq

-- created on 2026-09-22
-- updated on 2026-09-24
