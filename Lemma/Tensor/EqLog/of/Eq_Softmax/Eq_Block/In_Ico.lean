import sympy.functions.elementary.masked_softmax
import sympy.Basic


@[main]
private lemma main
  {n l u : ℕ}
  {A : Fin n → Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h : ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) = (A i j) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) < (i.val : ℤ) + u)), Real.exp (A i k))) :
-- imply
  ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → Real.log (maskedSoftmax (fun j => (A i j)) (fun j : Fin n => if ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) then 1 else 0) j) = z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) := by
-- proof
  have key : ∀ (p : Prop) [Decidable p] (x : ℝ), maskedExp x (if p then 1 else 0) = if p then Real.exp x else 0 := by
    intro p _ x
    by_cases hp : p
    ·
      simp [maskedExp, hp]
    ·
      simp [maskedExp, hp]
  have hpos : ∀ (i j : Fin n), ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → 0 < ∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) < (i.val : ℤ) + u)), Real.exp (A i k) := by
    intro i j hp
    exact Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hp⟩⟩
  intro i j hp
  simp only [maskedSoftmax, key]
  rw [← Finset.sum_filter, if_pos hp, h i j hp, Real.log_div (Real.exp_pos _).ne' (hpos i j hp).ne', Real.log_exp]


@[main]
private lemma tf
  {n l u : ℕ}
  {A : Fin n → Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h : ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) = (A i j) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) < (i.val : ℤ) + u)), Real.exp (A i k))) :
-- imply
  ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → Real.log (maskedSoftmax (fun j => (A i j)) (fun j : Fin n => if ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) then 1 else 0) j) = z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) := by
-- proof
  have key : ∀ (p : Prop) [Decidable p] (x : ℝ), maskedExp x (if p then 1 else 0) = if p then Real.exp x else 0 := by
    intro p _ x
    by_cases hp : p
    ·
      simp [maskedExp, hp]
    ·
      simp [maskedExp, hp]
  have hpos : ∀ (i j : Fin n), ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → 0 < ∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) < (i.val : ℤ) + u)), Real.exp (A i k) := by
    intro i j hp
    exact Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hp⟩⟩
  intro i j hp
  simp only [maskedSoftmax, key]
  rw [← Finset.sum_filter, if_pos hp, h i j hp, Real.log_div (Real.exp_pos _).ne' (hpos i j hp).ne', Real.log_exp]


@[main]
private lemma upper_triangle
  {n u : ℕ}
  {A : Fin n → Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h : ∀ i j : Fin n, ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → z i ((j.val : ℤ) - i.val) = (A i j) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) ≤ (k.val : ℤ) ∧ (k.val : ℤ) < (i.val : ℤ) + u)), Real.exp (A i k))) :
-- imply
  ∀ i j : Fin n, ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → Real.log (maskedSoftmax (fun j => (A i j)) (fun j : Fin n => if ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) then 1 else 0) j) = z i ((j.val : ℤ) - i.val) := by
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
  intro i j hp
  simp only [maskedSoftmax, key]
  rw [← Finset.sum_filter, if_pos hp, h i j hp, Real.log_div (Real.exp_pos _).ne' (hpos i j hp).ne', Real.log_exp]


@[main]
private lemma upper_triangle.tf
  {n u : ℕ}
  {A : Fin n → Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h : ∀ i j : Fin n, ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → z i ((j.val : ℤ) - i.val) = (A i j) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) ≤ (k.val : ℤ) ∧ (k.val : ℤ) < (i.val : ℤ) + u)), Real.exp (A i k))) :
-- imply
  ∀ i j : Fin n, ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → Real.log (maskedSoftmax (fun j => (A i j)) (fun j : Fin n => if ((i.val : ℤ) ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) then 1 else 0) j) = z i ((j.val : ℤ) - i.val) := by
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
  intro i j hp
  simp only [maskedSoftmax, key]
  rw [← Finset.sum_filter, if_pos hp, h i j hp, Real.log_div (Real.exp_pos _).ne' (hpos i j hp).ne', Real.log_exp]


@[main]
private lemma lower_triangle
  {n l : ℕ}
  {A : Fin n → Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h : ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) → z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) = (A i j) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) ≤ i.val)), Real.exp (A i k))) :
-- imply
  ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) → Real.log (maskedSoftmax (fun j => (A i j)) (fun j : Fin n => if ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) then 1 else 0) j) = z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) := by
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
  intro i j hp
  simp only [maskedSoftmax, key]
  rw [← Finset.sum_filter, if_pos hp, h i j hp, Real.log_div (Real.exp_pos _).ne' (hpos i j hp).ne', Real.log_exp]


@[main]
private lemma lower_triangle.tf
  {n l : ℕ}
  {A : Fin n → Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h : ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) → z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) = (A i j) - Real.log (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) ≤ i.val)), Real.exp (A i k))) :
-- imply
  ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) → Real.log (maskedSoftmax (fun j => (A i j)) (fun j : Fin n => if ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) ≤ i.val) then 1 else 0) j) = z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) := by
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
  intro i j hp
  simp only [maskedSoftmax, key]
  rw [← Finset.sum_filter, if_pos hp, h i j hp, Real.log_div (Real.exp_pos _).ne' (hpos i j hp).ne', Real.log_exp]


-- created on 2026-09-27
