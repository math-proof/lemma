import sympy.functions.elementary.masked_softmax
import sympy.Basic


@[main]
private lemma relative_distance.lower_triangle
  {n l : ℕ}
  {c : ℤ}
  {w : ℤ → ℝ}
  {r : Fin n → ℤ}
  {d : ℕ}
  {C : Fin n → Fin d → ℝ}
  {A : Fin n → Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h : ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) → z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) = (A i j + w (c + max (-c) (min (r j - r i) c)) * (1 + ∑ t, C i t / Real.sqrt (∑ s, C i s ^ 2) * (C j t / Real.sqrt (∑ s, C j s ^ 2)))) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) ≤ i.val)), Real.exp (A i k + w (c + max (-c) (min (r k - r i) c)) * (1 + ∑ t, C i t / Real.sqrt (∑ s, C i s ^ 2) * (C k t / Real.sqrt (∑ s, C k s ^ 2)))))) :
-- imply
  ∀ i j : Fin n, maskedSoftmax (fun j => (A i j + w (c + max (-c) (min (r j - r i) c)) * (1 + ∑ t, C i t / Real.sqrt (∑ s, C i s ^ 2) * (C j t / Real.sqrt (∑ s, C j s ^ 2))))) (fun j : Fin n => if ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) then 1 else 0) j = if ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) then Real.exp (z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1))) else 0 := by
-- proof
  have key : ∀ (p : Prop) [Decidable p] (x : ℝ), maskedExp x (if p then 1 else 0) = if p then Real.exp x else 0 := by
    intro p _ x
    by_cases hp : p
    ·
      simp [maskedExp, hp]
    ·
      simp [maskedExp, hp]
  have hpos : ∀ (i j : Fin n), ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) → 0 < ∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) ≤ i.val)), Real.exp (A i k + w (c + max (-c) (min (r k - r i) c)) * (1 + ∑ t, C i t / Real.sqrt (∑ s, C i s ^ 2) * (C k t / Real.sqrt (∑ s, C k s ^ 2)))) := by
    intro i j hp
    exact Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hp⟩⟩
  intro i j
  simp only [maskedSoftmax, key]
  rw [← Finset.sum_filter]
  by_cases hp : ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val)
  ·
    simp only [if_pos hp]
    rw [h i j hp, Real.exp_sub, Real.exp_log (hpos i j hp)]
  ·
    simp only [if_neg hp, zero_div]


-- created on 2026-09-27
