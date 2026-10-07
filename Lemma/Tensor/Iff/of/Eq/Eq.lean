import Mathlib.Algebra.Order.BigOperators.Group.Finset
import sympy.concrete.expr_with_limits
import Mathlib.Analysis.InnerProductSpace.PiL2
import sympy.Basic
import Lemma.Finset.Eq.of.In.In.Lt.Lt.EqBiUnion.EqSum_Card


@[main]
private lemma kmeans
  {M k : ℕ}
  {w : ℕ → Finset ℕ}
  {i j : ℕ}
-- given
  (h₀ : ∑ i ∈ Finset.range k, (w i).card = M)
  (h₁ : (Finset.range k).biUnion w = Finset.range M) :
-- imply
  (j ∈ w i ∧ i < k) ↔ (i = ∑ i' ∈ Finset.range k, i' * (if j ∈ w i' then 1 else 0) ∧ j < M) := by
-- proof
  have hsum : ∀ i0, i0 < k → j ∈ w i0 → ∑ i' ∈ Finset.range k, i' * (if j ∈ w i' then 1 else 0) = i0 := by
    intro i0 hi0 hj
    rw [Finset.sum_eq_single i0]
    · simp [hj]
    · intro b hb hne
      rw [if_neg (fun hb' => hne (Finset.Eq.of.In.In.Lt.Lt.EqBiUnion.EqSum_Card h₀ h₁ (Finset.mem_range.mp hb) hi0 hb' hj)), mul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr hi0) h
  constructor
  · rintro ⟨hj, hi⟩
    refine ⟨(hsum i hi hj).symm, ?_⟩
    have : j ∈ (Finset.range k).biUnion w := Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, hj⟩
    rw [h₁] at this
    exact Finset.mem_range.mp this
  · rintro ⟨hi, hj⟩
    have : j ∈ (Finset.range k).biUnion w := by
      rw [h₁]
      exact Finset.mem_range.mpr hj
    obtain ⟨i0, hi0, hj0⟩ := Finset.mem_biUnion.mp this
    rw [hsum i0 (Finset.mem_range.mp hi0) hj0] at hi
    subst hi
    exact ⟨hj0, Finset.mem_range.mp hi0⟩


@[main]
private lemma kmeans.w_quote
  {M k d : ℕ} [NeZero k]
  {w w' : ℕ → Finset ℕ}
  {x : ℕ → EuclideanSpace ℝ (Fin d)}
  {i j : ℕ}
-- given
  (_h₀ : ∑ i ∈ Finset.range k, (w i).card = M)
  (_h₁ : (Finset.range k).biUnion w = Finset.range M)
  (h₂ : ∀ i, w' i = (Finset.range M).filter fun j => ((ArgMin Set.univ (fun i' : Fin k => ‖x j - (((w i').card : ℝ)⁻¹ • ∑ j' ∈ w i', x j')‖) : Fin k) : ℕ) = i) :
-- imply
  (j ∈ w' i ∧ i < k) ↔ (i = ((ArgMin Set.univ (fun i' : Fin k => ‖x j - (((w i').card : ℝ)⁻¹ • ∑ j' ∈ w i', x j')‖) : Fin k) : ℕ) ∧ j < M) := by
-- proof
  rw [h₂]
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨hj, e⟩, _⟩
    exact ⟨e.symm, hj⟩
  · rintro ⟨e, hj⟩
    exact ⟨⟨hj, e.symm⟩, by rw [e]; exact Fin.isLt _⟩


-- created on 2026-09-27
