import sympy.stats.stochastic_process_types
import Lemma.Matrix.Any_All_Gt_0.of.DoeblinMinorization
import Lemma.Matrix.GetPow_Add.ge.MulGetSPow
import Lemma.Matrix.Any_All_Imp_Gt_0.of.Aperiodic.StochasticIrreducible
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Finset.Lattice.Fold


/--
| attributes | lemma |
| :---: | :---: |
| main | Matrix.Any_And_DoeblinMinorizationPow.is.Nonempty.Aperiodic |
| comm | Matrix.Nonempty.Aperiodic.is.Any_And_DoeblinMinorizationPow |
| mp | Matrix.Nonempty.Aperiodic.of.Any_And_DoeblinMinorizationPow |
| mpr | Matrix.Any_And_DoeblinMinorizationPow.of.Nonempty.Aperiodic |
-/
@[main, comm, mp, mpr]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {P : Matrix S S ℝ} [RowStochastic P] [StochasticIrreducible P] :
-- imply
  (∃ N, 1 ≤ N ∧ DoeblinMinorization (P ^ N)) ↔ Nonempty S ∧ Aperiodic P := by
-- proof
  constructor
  · intro h
    have hNe : Nonempty S := by
      obtain ⟨_, _, hDoeblin⟩ := h
      obtain ⟨_, ν, _, _, hν, _⟩ := hDoeblin.minorize
      by_contra hS
      rw [not_nonempty_iff] at hS
      have := hν.rowsum
      simp at this
    refine ⟨hNe, ?_⟩
    obtain ⟨N, hN1, hDoeblin⟩ := h
    obtain ⟨j₀, hj₀⟩ := Matrix.Any_All_Gt_0.of.DoeblinMinorization (P := P ^ N) hDoeblin
    have hPN1 : ∀ i, 0 < (P ^ (N + 1)) i j₀ := by
      intro i
      have hrow := (inferInstance : RowStochastic P).stochastic i
      obtain ⟨k, hk⟩ : ∃ k, 0 < P i k := by
        by_contra hnone
        push Not at hnone
        have hz : ∀ k, P i k = 0 := fun k =>
          le_antisymm (hnone k) (hrow.nonneg k)
        have : ∑ k, P i k = 0 := Finset.sum_eq_zero fun k _ => hz k
        linarith [hrow.rowsum]
      have hineq := (@Matrix.GetPow_Add.ge.MulGetSPow _ _ _ P _ 1 N i j₀ k).le
      rw [pow_one, Nat.add_comm] at hineq
      exact lt_of_lt_of_le (mul_pos hk (hj₀ k)) hineq
    refine ⟨fun i => ?_⟩
    obtain ⟨b, hb⟩ := (inferInstance : StochasticIrreducible P).irreducible j₀ i
    let n₁ := N + b
    let n₂ := N + 1 + b
    have hn₁ge : 1 ≤ n₁ := by
      simp only [n₁]
      omega
    have hn₂ge : 1 ≤ n₂ := by
      simp only [n₂]
      omega
    have hn₁pos : 0 < (P ^ n₁) i i := by
      calc
        0
        _ < (P ^ N) i j₀ * (P ^ b) j₀ i := mul_pos (hj₀ i) hb
        _ ≤ (P ^ n₁) i i := by
          simp only [n₁]
          exact (@Matrix.GetPow_Add.ge.MulGetSPow _ _ _ P _ N b i i j₀).le
    have hn₂pos : 0 < (P ^ n₂) i i := by
      calc
        0
        _ < (P ^ (N + 1)) i j₀ * (P ^ b) j₀ i := mul_pos (hPN1 i) hb
        _ ≤ (P ^ n₂) i i := by
          simp only [n₂]
          exact (@Matrix.GetPow_Add.ge.MulGetSPow _ _ _ P _ (N + 1) b i i j₀).le
    refine ⟨{n₁, n₂}, ?_, ?_, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
      obtain (rfl | rfl) := hx
      · exact ⟨hn₁ge, hn₁pos⟩
      · exact ⟨hn₂ge, hn₂pos⟩
    · rw [Finset.gcd_insert, Finset.gcd_singleton, normalize_eq, id_eq, id_eq]
      change Nat.gcd n₁ n₂ = 1
      have hEq : n₂ = n₁ + 1 := by
        simp only [n₁, n₂]
        omega
      rw [hEq, Nat.gcd_self_add_right, Nat.gcd_one_right]
    · intro h0
      simp only [Finset.mem_insert, Finset.mem_singleton] at h0
      obtain (h0 | h0) := h0
      ·
        simp only [n₁] at h0
        omega
      ·
        simp only [n₂] at h0
        omega
    · simp
  · rintro ⟨hNe, hAper⟩
    have : Nonempty S := hNe
    have : Aperiodic P := hAper
    obtain ⟨n₀, hn₀⟩ := Matrix.Any_All_Imp_Gt_0.of.Aperiodic.StochasticIrreducible inferInstance hAper
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

-- created on 2026-09-24
