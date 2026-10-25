/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Def.Analysis.NormedSpace.RosenthalL1.Part10
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace FunctionalAnalysis.RosenthalL1Wanted

theorem rosenthal_pairsHold_initial_even {K : Type*}
    (R : K → ℕ → ℕ → Prop) (k : K) (φ : ℕ → ℕ) :
    ∀ N, rosenthalPairsHold R k (rosenthalInitialSegment φ (2 * N)) ↔
      ∀ j < N, R k (φ (2 * j)) (φ (2 * j + 1)) := by
  intro N
  induction N generalizing φ with
  | zero => simp [rosenthalInitialSegment, rosenthalPairsHold]
  | succ N ih =>
      rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
        rosenthal_initialSegment_succ, rosenthal_initialSegment_succ]
      simp only [rosenthalPairsHold]
      rw [ih]
      constructor
      · rintro ⟨hzero, htail⟩ j hj
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · simpa [rosenthalTail] using hzero
        · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hjpos)
          have hi : i < N := by omega
          change R k (φ (2 * (i + 1))) (φ (2 * (i + 1) + 1))
          simpa [rosenthalTail, mul_add, add_assoc] using htail i hi
      · intro h
        refine ⟨?_, ?_⟩
        · simpa [rosenthalTail] using h 0 (Nat.zero_lt_succ N)
        · intro i hi
          change R k (φ (2 * i + 1 + 1)) (φ (2 * i + 1 + 1 + 1))
          simpa [rosenthalTail, mul_add, add_assoc] using h (i + 1) (by omega)

theorem rosenthal_exists_finite_pair_obstruction
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (R : K → ℕ → ℕ → Prop) (hclosed : ∀ i j, IsClosed {k | R k i j})
    (φ : ℕ → ℕ) (h : ¬∃ k, ∀ n, R k (φ (2 * n)) (φ (2 * n + 1))) :
    ∃ N, ¬∃ k, ∀ n < N, R k (φ (2 * n)) (φ (2 * n + 1)) := by
  let U : ℕ → Set K := fun n => {k | ¬R k (φ (2 * n)) (φ (2 * n + 1))}
  have hopen : ∀ n, IsOpen (U n) := by
    intro n
    exact (hclosed _ _).isOpen_compl
  have hcover : Set.univ ⊆ ⋃ n, U n := by
    intro k hk
    rw [Set.mem_iUnion]
    by_contra hnone
    push Not at hnone
    have hall : ∀ n, R k (φ (2 * n)) (φ (2 * n + 1)) := by
      intro n
      simpa only [U, Set.mem_ofPred_eq, not_not] using hnone n
    exact h ⟨k, hall⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
  refine ⟨t.sup id + 1, ?_⟩
  rintro ⟨k, hk⟩
  have hkt := ht (Set.mem_univ k)
  simp only [Set.mem_iUnion] at hkt
  obtain ⟨n, hnmem, hnU⟩ := hkt
  have hnlt : n < t.sup id + 1 :=
    Nat.lt_succ_of_le (Finset.le_sup (f := id) hnmem)
  exact hnU (hk n hnlt)

end FunctionalAnalysis.RosenthalL1Wanted
