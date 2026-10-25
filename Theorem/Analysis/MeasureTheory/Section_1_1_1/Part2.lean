import Def.Analysis.MeasureTheory.Notation.Part2
import Theorem.Analysis.Section_9_1.Part3
import Instance.Analysis.MeasureTheory.Section_1_1_1.Part2
open BoundedInterval


/-- Simp lemmas for coercing each {name}`BoundedInterval` constructor to {lean}`Set ℝ`. -/
@[simp]
theorem BoundedInterval.set_Ioo (a b:ℝ) : (Ioo a b : Set ℝ) = .Ioo a b := by rfl

@[simp]
theorem BoundedInterval.set_Icc (a b:ℝ) : (Icc a b : Set ℝ) = .Icc a b := by rfl

@[simp]
theorem BoundedInterval.set_Ioc (a b:ℝ) : (Ioc a b : Set ℝ) = .Ioc a b := by rfl

@[simp]
theorem BoundedInterval.set_Ico (a b:ℝ) : (Ico a b : Set ℝ) = .Ico a b := by rfl

/-- Some helpful general lemmas about {name}`BoundedInterval` -/
theorem Bornology.IsBounded.of_boundedInterval (I: BoundedInterval) : Bornology.IsBounded (I:Set ℝ) := by
  cases I with
  | Ioo a b =>
    simp [set_Ioo]
    exact Metric.isBounded_Ioo a b
  | Icc a b =>
    simp [set_Icc]
    exact Metric.isBounded_Icc a b
  | Ioc a b =>
    simp [set_Ioc]
    exact Metric.isBounded_Ioc a b
  | Ico a b =>
    simp [set_Ico]
    exact Metric.isBounded_Ico a b

namespace BoundedInterval

/-- Extract endpoints from {name}`BoundedInterval.Icc` equality -/
lemma Icc_eq_endpoints {a₁ b₁ a₂ b₂ : ℝ}
    (h : Set.Icc a₁ b₁ = Set.Icc a₂ b₂) (ha₁b₁ : a₁ ≤ b₁) (ha₂b₂ : a₂ ≤ b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  constructor
  · have h₁ : a₁ ∈ Set.Icc a₁ b₁ := by simp [Set.mem_Icc, ha₁b₁]
    rw [h] at h₁; simp [Set.mem_Icc] at h₁
    have h₂ : a₂ ∈ Set.Icc a₂ b₂ := by simp [Set.mem_Icc, ha₂b₂]
    rw [← h] at h₂; simp [Set.mem_Icc] at h₂
    linarith
  · have h₁ : b₁ ∈ Set.Icc a₁ b₁ := by simp [Set.mem_Icc, ha₁b₁]
    rw [h] at h₁; simp [Set.mem_Icc] at h₁
    have h₂ : b₂ ∈ Set.Icc a₂ b₂ := by simp [Set.mem_Icc, ha₂b₂]
    rw [← h] at h₂; simp [Set.mem_Icc] at h₂
    linarith

/-- {name}`BoundedInterval.Ioo` cannot equal {name}`BoundedInterval.Icc` -/
lemma Ioo_ne_Icc {a₁ b₁ a₂ b₂ : ℝ} (ha₁b₁ : a₁ < b₁) (ha₂b₂ : a₂ ≤ b₂) :
    Set.Ioo a₁ b₁ ≠ Set.Icc a₂ b₂ := by
  intro h
  have h_cl := congr_arg closure h
  rw [closure_Ioo ha₁b₁.ne, isClosed_Icc.closure_eq] at h_cl
  obtain ⟨ha, hb⟩ := Icc_eq_endpoints h_cl (le_of_lt ha₁b₁) ha₂b₂
  have : a₂ ∉ Set.Ioo a₁ b₁ := by simp [Set.mem_Ioo]; intro; linarith
  have : a₂ ∈ Set.Icc a₂ b₂ := by simp [Set.mem_Icc, ha₂b₂]
  rw [← h] at this
  contradiction

/-- {name}`BoundedInterval.Ioo` cannot equal {name}`BoundedInterval.Ioc` -/
lemma Ioo_ne_Ioc {a₁ b₁ a₂ b₂ : ℝ} (ha₁b₁ : a₁ < b₁) (ha₂b₂ : a₂ < b₂) :
    Set.Ioo a₁ b₁ ≠ Set.Ioc a₂ b₂ := by
  intro h
  have h_cl := congr_arg closure h
  rw [closure_Ioo ha₁b₁.ne, closure_Ioc ha₂b₂.ne] at h_cl
  obtain ⟨_, hb⟩ := Icc_eq_endpoints h_cl (le_of_lt ha₁b₁) (le_of_lt ha₂b₂)
  have : b₂ ∈ Set.Ioc a₂ b₂ := ⟨ha₂b₂, le_refl b₂⟩
  rw [← h] at this
  simp [Set.mem_Ioo] at this
  linarith

/-- {name}`BoundedInterval.Ioo` cannot equal {name}`BoundedInterval.Ico` -/
lemma Ioo_ne_Ico {a₁ b₁ a₂ b₂ : ℝ} (ha₁b₁ : a₁ < b₁) (ha₂b₂ : a₂ < b₂) :
    Set.Ioo a₁ b₁ ≠ Set.Ico a₂ b₂ := by
  intro h
  have h_cl := congr_arg closure h
  rw [closure_Ioo ha₁b₁.ne, closure_Ico ha₂b₂.ne] at h_cl
  obtain ⟨ha, _⟩ := Icc_eq_endpoints h_cl (le_of_lt ha₁b₁) (le_of_lt ha₂b₂)
  have : a₂ ∈ Set.Ico a₂ b₂ := ⟨le_refl a₂, ha₂b₂⟩
  rw [← h] at this
  simp [Set.mem_Ioo] at this
  linarith

/-- {name}`BoundedInterval.Ioc` cannot equal {name}`BoundedInterval.Ico` -/
lemma Ioc_ne_Ico {a₁ b₁ a₂ b₂ : ℝ} (ha₁b₁ : a₁ < b₁) (ha₂b₂ : a₂ < b₂) :
    Set.Ioc a₁ b₁ ≠ Set.Ico a₂ b₂ := by
  intro h
  have h_cl := congr_arg closure h
  rw [closure_Ioc ha₁b₁.ne, closure_Ico ha₂b₂.ne] at h_cl
  obtain ⟨_, hb⟩ := Icc_eq_endpoints h_cl (le_of_lt ha₁b₁) (le_of_lt ha₂b₂)
  have : b₁ ∈ Set.Ioc a₁ b₁ := ⟨ha₁b₁, le_refl b₁⟩
  rw [h] at this
  simp [Set.mem_Ico] at this
  linarith

/-- {name}`BoundedInterval.Icc` cannot equal {name}`BoundedInterval.Ioc` -/
lemma Icc_ne_Ioc {a₁ b₁ a₂ b₂ : ℝ} (ha₁b₁ : a₁ ≤ b₁) (ha₂b₂ : a₂ < b₂) :
    Set.Icc a₁ b₁ ≠ Set.Ioc a₂ b₂ := by
  intro h
  have h_cl := congr_arg closure h
  rw [isClosed_Icc.closure_eq, closure_Ioc ha₂b₂.ne] at h_cl
  obtain ⟨ha, _⟩ := Icc_eq_endpoints h_cl ha₁b₁ (le_of_lt ha₂b₂)
  have : a₁ ∈ Set.Icc a₁ b₁ := by simp [Set.mem_Icc, ha₁b₁]
  rw [h] at this
  simp [Set.mem_Ioc] at this
  linarith

/-- {name}`BoundedInterval.Icc` cannot equal {name}`BoundedInterval.Ico` -/
lemma Icc_ne_Ico {a₁ b₁ a₂ b₂ : ℝ} (ha₁b₁ : a₁ ≤ b₁) (ha₂b₂ : a₂ < b₂) :
    Set.Icc a₁ b₁ ≠ Set.Ico a₂ b₂ := by
  intro h
  have h_cl := congr_arg closure h
  rw [isClosed_Icc.closure_eq, closure_Ico ha₂b₂.ne] at h_cl
  obtain ⟨_, hb⟩ := Icc_eq_endpoints h_cl ha₁b₁ (le_of_lt ha₂b₂)
  have : b₁ ∈ Set.Icc a₁ b₁ := by simp [Set.mem_Icc, ha₁b₁]
  rw [h] at this
  simp [Set.mem_Ico] at this
  linarith

/-- Extract that a < b from nonempty {name}`BoundedInterval.Ioo` -/
private lemma nonempty_Ioo_strictness {a b : ℝ} (h : (Ioo a b).toSet.Nonempty) : a < b := by
  obtain ⟨x, hx⟩ := h
  simp [toSet] at hx
  exact hx.1.trans hx.2

/-- Extract that a < b from nonempty {name}`BoundedInterval.Ioc` -/
private lemma nonempty_Ioc_strictness {a b : ℝ} (h : (Ioc a b).toSet.Nonempty) : a < b := by
  obtain ⟨x, hx⟩ := h
  simp [toSet] at hx
  exact hx.1.trans_le hx.2

/-- Extract that a < b from nonempty {name}`BoundedInterval.Ico` -/
private lemma nonempty_Ico_strictness {a b : ℝ} (h : (Ico a b).toSet.Nonempty) : a < b := by
  obtain ⟨x, hx⟩ := h
  simp [toSet] at hx
  exact hx.1.trans_lt hx.2

/-- Extract that a ≤ b from nonempty {name}`BoundedInterval.Icc` -/
private lemma nonempty_Icc_order {a b : ℝ} (h : (Icc a b).toSet.Nonempty) : a ≤ b := by
  obtain ⟨x, hx⟩ := h
  simp [toSet] at hx
  exact hx.1.trans hx.2

/-- Extract equal endpoints from equal {name}`BoundedInterval.Icc` sets -/
private lemma endpoints_of_Icc_eq {a₁ b₁ a₂ b₂ : ℝ}
    (h_closure : Set.Icc a₁ b₁ = Set.Icc a₂ b₂) (ha₁b₁ : a₁ ≤ b₁) (ha₂b₂ : a₂ ≤ b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  constructor
  · have h₁ : a₁ ∈ Set.Icc a₁ b₁ := by simp [Set.mem_Icc, ha₁b₁]
    rw [h_closure] at h₁; simp [Set.mem_Icc] at h₁
    have h₂ : a₂ ∈ Set.Icc a₂ b₂ := by simp [Set.mem_Icc, ha₂b₂]
    rw [← h_closure] at h₂; simp [Set.mem_Icc] at h₂
    linarith
  · have h₁ : b₁ ∈ Set.Icc a₁ b₁ := by simp [Set.mem_Icc, ha₁b₁]
    rw [h_closure] at h₁; simp [Set.mem_Icc] at h₁
    have h₂ : b₂ ∈ Set.Icc a₂ b₂ := by simp [Set.mem_Icc, ha₂b₂]
    rw [← h_closure] at h₂; simp [Set.mem_Icc] at h₂
    linarith

/-- {name}`BoundedInterval.toSet` is injective for non-empty intervals -/
lemma toSet_injective_of_nonempty {I J : BoundedInterval}
    (hI : I.toSet.Nonempty) (hJ : J.toSet.Nonempty) (h_eq : I.toSet = J.toSet) :
    I = J := by
  -- Case analysis on both intervals (16 cases total)
  cases I with
  | Ioo a₁ b₁ =>
    cases J with
    | Ioo a₂ b₂ =>
      -- Ioo a₁ b₁ = Ioo a₂ b₂: use closure to extract endpoints
      have ha₁b₁ := nonempty_Ioo_strictness hI
      have ha₂b₂ := nonempty_Ioo_strictness hJ
      have h_set_eq : Set.Ioo a₁ b₁ = Set.Ioo a₂ b₂ := h_eq
      have h_closure : closure (Set.Ioo a₁ b₁) = closure (Set.Ioo a₂ b₂) := by rw [h_set_eq]
      rw [closure_Ioo ha₁b₁.ne, closure_Ioo ha₂b₂.ne] at h_closure
      obtain ⟨ha, hb⟩ := endpoints_of_Icc_eq h_closure ha₁b₁.le ha₂b₂.le
      rw [ha, hb]
    | Icc a₂ b₂ =>
      exact absurd h_eq (Ioo_ne_Icc (nonempty_Ioo_strictness hI) (nonempty_Icc_order hJ))
    | Ioc a₂ b₂ =>
      exact absurd h_eq (Ioo_ne_Ioc (nonempty_Ioo_strictness hI) (nonempty_Ioc_strictness hJ))
    | Ico a₂ b₂ =>
      exact absurd h_eq (Ioo_ne_Ico (nonempty_Ioo_strictness hI) (nonempty_Ico_strictness hJ))
  | Icc a₁ b₁ =>
    cases J with
    | Ioo a₂ b₂ =>
      exact absurd h_eq.symm (Ioo_ne_Icc (nonempty_Ioo_strictness hJ) (nonempty_Icc_order hI))
    | Icc a₂ b₂ =>
      -- Icc a₁ b₁ = Icc a₂ b₂: directly extract endpoints
      have ha₁b₁ := nonempty_Icc_order hI
      have ha₂b₂ := nonempty_Icc_order hJ
      obtain ⟨ha, hb⟩ := endpoints_of_Icc_eq h_eq ha₁b₁ ha₂b₂
      rw [ha, hb]
    | Ioc a₂ b₂ =>
      exact absurd h_eq (Icc_ne_Ioc (nonempty_Icc_order hI) (nonempty_Ioc_strictness hJ))
    | Ico a₂ b₂ =>
      exact absurd h_eq (Icc_ne_Ico (nonempty_Icc_order hI) (nonempty_Ico_strictness hJ))
  | Ioc a₁ b₁ =>
    cases J with
    | Ioo a₂ b₂ =>
      exact absurd h_eq.symm (Ioo_ne_Ioc (nonempty_Ioo_strictness hJ) (nonempty_Ioc_strictness hI))
    | Icc a₂ b₂ =>
      exact absurd h_eq.symm (Icc_ne_Ioc (nonempty_Icc_order hJ) (nonempty_Ioc_strictness hI))
    | Ioc a₂ b₂ =>
      -- Ioc a₁ b₁ = Ioc a₂ b₂: use closure like Ioo
      have ha₁b₁ := nonempty_Ioc_strictness hI
      have ha₂b₂ := nonempty_Ioc_strictness hJ
      have h_set_eq : Set.Ioc a₁ b₁ = Set.Ioc a₂ b₂ := h_eq
      have h_closure : closure (Set.Ioc a₁ b₁) = closure (Set.Ioc a₂ b₂) := by rw [h_set_eq]
      rw [closure_Ioc ha₁b₁.ne, closure_Ioc ha₂b₂.ne] at h_closure
      obtain ⟨ha, hb⟩ := endpoints_of_Icc_eq h_closure ha₁b₁.le ha₂b₂.le
      rw [ha, hb]
    | Ico a₂ b₂ =>
      exact absurd h_eq (Ioc_ne_Ico (nonempty_Ioc_strictness hI) (nonempty_Ico_strictness hJ))
  | Ico a₁ b₁ =>
    cases J with
    | Ioo a₂ b₂ =>
      exact absurd h_eq.symm (Ioo_ne_Ico (nonempty_Ioo_strictness hJ) (nonempty_Ico_strictness hI))
    | Icc a₂ b₂ =>
      exact absurd h_eq.symm (Icc_ne_Ico (nonempty_Icc_order hJ) (nonempty_Ico_strictness hI))
    | Ioc a₂ b₂ =>
      exact absurd h_eq.symm (Ioc_ne_Ico (nonempty_Ioc_strictness hJ) (nonempty_Ico_strictness hI))
    | Ico a₂ b₂ =>
      -- Ico a₁ b₁ = Ico a₂ b₂: use closure like Ioo
      have ha₁b₁ := nonempty_Ico_strictness hI
      have ha₂b₂ := nonempty_Ico_strictness hJ
      have h_set_eq : Set.Ico a₁ b₁ = Set.Ico a₂ b₂ := h_eq
      have h_closure : closure (Set.Ico a₁ b₁) = closure (Set.Ico a₂ b₂) := by rw [h_set_eq]
      rw [closure_Ico ha₁b₁.ne, closure_Ico ha₂b₂.ne] at h_closure
      obtain ⟨ha, hb⟩ := endpoints_of_Icc_eq h_closure ha₁b₁.le ha₂b₂.le
      rw [ha, hb]

end BoundedInterval
