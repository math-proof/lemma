import sympy.functions.elementary.masked_softmax
import sympy.Basic


@[main]
private lemma biased.lower_triangle.tf
  {n l : ℕ}
  {A : Fin n → Fin n → ℝ}
  {H : Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h : ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) → z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) = (A i j + if i = j then H i else 0) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) ≤ i.val)), Real.exp (A i k + if i = k then H i else 0))) :
-- imply
  ∀ i j : Fin n, maskedSoftmax (fun j => (A i j + if i = j then H i else 0)) (fun j : Fin n => if ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) then 1 else 0) j = if ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) then Real.exp (z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1))) else 0 := by
-- proof
  have key : ∀ (p : Prop) [Decidable p] (x : ℝ), maskedExp x (if p then 1 else 0) = if p then Real.exp x else 0 := by
    intro p _ x
    by_cases hp : p
    ·
      simp [maskedExp, hp]
    ·
      simp [maskedExp, hp]
  have hpos : ∀ (i j : Fin n), ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) → 0 < ∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) ≤ i.val)), Real.exp (A i k + if i = k then H i else 0) := by
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


@[main]
private lemma biased.upper_triangle.tf
  {n u : ℕ}
  {A : Fin n → Fin n → ℝ}
  {H : Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h : ∀ i j : Fin n, ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → z i ((j.val : ℤ) - i.val) = (A i j + if i = j then H i else 0) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) ≤ (k.val : ℤ) ∧ (k.val : ℤ) < (i.val : ℤ) + u)), Real.exp (A i k + if i = k then H i else 0))) :
-- imply
  ∀ i j : Fin n, maskedSoftmax (fun j => (A i j + if i = j then H i else 0)) (fun j : Fin n => if ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) then 1 else 0) j = if ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) then Real.exp (z i ((j.val : ℤ) - i.val)) else 0 := by
-- proof
  have key : ∀ (p : Prop) [Decidable p] (x : ℝ), maskedExp x (if p then 1 else 0) = if p then Real.exp x else 0 := by
    intro p _ x
    by_cases hp : p
    ·
      simp [maskedExp, hp]
    ·
      simp [maskedExp, hp]
  have hpos : ∀ (i j : Fin n), ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → 0 < ∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) ≤ (k.val : ℤ) ∧ (k.val : ℤ) < (i.val : ℤ) + u)), Real.exp (A i k + if i = k then H i else 0) := by
    intro i j hp
    exact Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hp⟩⟩
  intro i j
  simp only [maskedSoftmax, key]
  rw [← Finset.sum_filter]
  by_cases hp : ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u)
  ·
    simp only [if_pos hp]
    rw [h i j hp, Real.exp_sub, Real.exp_log (hpos i j hp)]
  ·
    simp only [if_neg hp, zero_div]


@[main]
private lemma bilinear_matrix_attention.biased.lower_triangle.tf
  {n l : ℕ}
  {d : ℕ}
  {Q K : Fin n → Fin d → ℝ}
  {W : Fin d → Fin d → ℝ}
  {H : Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h : ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) → z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) = ((∑ s, ∑ t, Q i s * W s t * K j t) + if i = j then H i else 0) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) ≤ i.val)), Real.exp ((∑ s, ∑ t, Q i s * W s t * K k t) + if i = k then H i else 0))) :
-- imply
  ∀ i j : Fin n, maskedSoftmax (fun j => ((∑ s, ∑ t, Q i s * W s t * K j t) + if i = j then H i else 0)) (fun j : Fin n => if ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) then 1 else 0) j = if ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) then Real.exp (z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1))) else 0 := by
-- proof
  have key : ∀ (p : Prop) [Decidable p] (x : ℝ), maskedExp x (if p then 1 else 0) = if p then Real.exp x else 0 := by
    intro p _ x
    by_cases hp : p
    ·
      simp [maskedExp, hp]
    ·
      simp [maskedExp, hp]
  have hpos : ∀ (i j : Fin n), ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) → 0 < ∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) ≤ i.val)), Real.exp ((∑ s, ∑ t, Q i s * W s t * K k t) + if i = k then H i else 0) := by
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


@[main]
private lemma lower_triangle.tf
  {n l : ℕ}
  {A : Fin n → Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h : ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) → z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) = (A i j) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) ≤ i.val)), Real.exp (A i k))) :
-- imply
  ∀ i j : Fin n, maskedSoftmax (fun j => (A i j)) (fun j : Fin n => if ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) then 1 else 0) j = if ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) then Real.exp (z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1))) else 0 := by
-- proof
  have key : ∀ (p : Prop) [Decidable p] (x : ℝ), maskedExp x (if p then 1 else 0) = if p then Real.exp x else 0 := by
    intro p _ x
    by_cases hp : p
    ·
      simp [maskedExp, hp]
    ·
      simp [maskedExp, hp]
  have hpos : ∀ (i j : Fin n), ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) → 0 < ∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) ≤ i.val)), Real.exp (A i k) := by
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


@[main]
private lemma upper_triangle.tf
  {n u : ℕ}
  {A : Fin n → Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h : ∀ i j : Fin n, ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → z i ((j.val : ℤ) - i.val) = (A i j) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) ≤ (k.val : ℤ) ∧ (k.val : ℤ) < (i.val : ℤ) + u)), Real.exp (A i k))) :
-- imply
  ∀ i j : Fin n, maskedSoftmax (fun j => (A i j)) (fun j : Fin n => if ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) then 1 else 0) j = if ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) then Real.exp (z i ((j.val : ℤ) - i.val)) else 0 := by
-- proof
  have key : ∀ (p : Prop) [Decidable p] (x : ℝ), maskedExp x (if p then 1 else 0) = if p then Real.exp x else 0 := by
    intro p _ x
    by_cases hp : p
    ·
      simp [maskedExp, hp]
    ·
      simp [maskedExp, hp]
  have hpos : ∀ (i j : Fin n), ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → 0 < ∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) ≤ (k.val : ℤ) ∧ (k.val : ℤ) < (i.val : ℤ) + u)), Real.exp (A i k) := by
    intro i j hp
    exact Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hp⟩⟩
  intro i j
  simp only [maskedSoftmax, key]
  rw [← Finset.sum_filter]
  by_cases hp : ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u)
  ·
    simp only [if_pos hp]
    rw [h i j hp, Real.exp_sub, Real.exp_log (hpos i j hp)]
  ·
    simp only [if_neg hp, zero_div]


@[main]
private lemma lower_triangle
  {n l : ℕ}
  {A : Fin n → Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h : ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) → z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) = (A i j) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) ≤ i.val)), Real.exp (A i k))) :
-- imply
  ∀ i j : Fin n, maskedSoftmax (fun j => (A i j)) (fun j : Fin n => if ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) then 1 else 0) j = if ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) then Real.exp (z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1))) else 0 := by
-- proof
  have key : ∀ (p : Prop) [Decidable p] (x : ℝ), maskedExp x (if p then 1 else 0) = if p then Real.exp x else 0 := by
    intro p _ x
    by_cases hp : p
    ·
      simp [maskedExp, hp]
    ·
      simp [maskedExp, hp]
  have hpos : ∀ (i j : Fin n), ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) → 0 < ∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) ≤ i.val)), Real.exp (A i k) := by
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
