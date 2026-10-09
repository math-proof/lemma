import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lemma.Finset.Eq.of.In.In.Lt.Lt.EqBiUnion.EqSum_Card
open Finset


@[main]
private lemma main
  {M k : ℕ}
  {w : ℕ → Finset ℕ}
  {i j : ℕ}
-- given
  (h₀ : ∑ i ∈ Finset.range k, (w i).card = M)
  (h₁ : (Finset.range k).biUnion w = Finset.range M) :
-- imply
  (j ∈ w i ∧ i < k) ↔
    (i = ∑ i' ∈ Finset.range k, i' * (if j ∈ w i' then 1 else 0) ∧ j < M) := by
-- proof
  have hsum : ∀ i0, i0 < k → j ∈ w i0 →
      ∑ i' ∈ Finset.range k, i' * (if j ∈ w i' then 1 else 0) = i0 := by
    intro i0 hi0 hj
    rw [Finset.sum_eq_single i0]
    · simp [hj]
    ·
      intro b hb hne
      rw [ite_eq_right (fun hb' =>
        hne (Eq.of.In.In.Lt.Lt.EqBiUnion.EqSum_Card
          h₀ h₁ (Finset.mem_range.mp hb) hi0 hb' hj)), mul_zero]
    ·
      intro h
      exact absurd (Finset.mem_range.mpr hi0) h
  constructor
  ·
    rintro ⟨hj, hi⟩
    refine ⟨(hsum i hi hj).symm, ?_⟩
    have : j ∈ (Finset.range k).biUnion w :=
      Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, hj⟩
    rw [h₁] at this
    exact Finset.mem_range.mp this
  ·
    rintro ⟨hi, hj⟩
    have : j ∈ (Finset.range k).biUnion w := by
      rw [h₁]
      exact Finset.mem_range.mpr hj
    obtain ⟨i0, hi0, hj0⟩ := Finset.mem_biUnion.mp this
    rw [hsum i0 (Finset.mem_range.mp hi0) hj0] at hi
    subst hi
    exact ⟨hj0, Finset.mem_range.mp hi0⟩


-- created on 2026-10-09
