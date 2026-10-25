import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part3
open Pointwise


/-- The Cartesian product of bounded sets is bounded. -/
lemma EuclideanSpace'.norm_prod_equiv_symm {d₁ d₂:ℕ}
    (y : EuclideanSpace' d₁) (z : EuclideanSpace' d₂) :
    ‖(EuclideanSpace'.prod_equiv d₁ d₂).symm (y, z)‖ ^ 2 = ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
  have hy : 0 ≤ ∑ i : Fin d₁, (y i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hz : 0 ≤ ∑ j : Fin d₂, (z j) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsum : 0 ≤ ∑ i : Fin (d₁ + d₂), ((EuclideanSpace'.prod_equiv d₁ d₂).symm (y, z) i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  simp only [EuclideanSpace'.norm_eq, Real.sq_sqrt hsum, Real.sq_sqrt hy, Real.sq_sqrt hz]
  rw [Fin.sum_univ_add]
  refine congrArg₂ (· + ·) ?_ ?_
  · apply Finset.sum_congr rfl
    intro i _
    have hi := i.isLt
    have : Fin.castAdd d₂ i = ⟨(i : ℕ), Nat.lt_add_right d₂ hi⟩ := by
      ext; simp [Fin.castAdd]
    rw [this, EuclideanSpace'.prod_equiv_symm_apply_left y z hi]
  · apply Finset.sum_congr rfl
    intro j _
    have hj := j.isLt
    have : Fin.natAdd d₁ j = ⟨d₁ + (j : ℕ), Nat.add_lt_add_left hj d₁⟩ := by
      ext; simp [Fin.natAdd]
    rw [this, EuclideanSpace'.prod_equiv_symm_apply_right y z hj]

lemma EuclideanSpace'.prod_mono {d₁ d₂:ℕ}
    {E₁ E₁' : Set (EuclideanSpace' d₁)} {E₂ E₂' : Set (EuclideanSpace' d₂)}
    (h₁ : E₁ ⊆ E₁') (h₂ : E₂ ⊆ E₂') :
    EuclideanSpace'.prod E₁ E₂ ⊆ EuclideanSpace'.prod E₁' E₂' :=
  Set.image_mono (Set.prod_mono h₁ h₂)

lemma EuclideanSpace'.prod_isBounded {d₁ d₂:ℕ}
    {E₁ : Set (EuclideanSpace' d₁)} {E₂ : Set (EuclideanSpace' d₂)}
    (hE₁ : Bornology.IsBounded E₁) (hE₂ : Bornology.IsBounded E₂) :
    Bornology.IsBounded (EuclideanSpace'.prod E₁ E₂) := by
  rw [Metric.isBounded_iff_subset_closedBall 0] at hE₁ hE₂ ⊢
  obtain ⟨M₁, hM₁⟩ := hE₁
  obtain ⟨M₂, hM₂⟩ := hE₂
  refine ⟨Real.sqrt (M₁ ^ 2 + M₂ ^ 2), ?_⟩
  intro x hx
  obtain ⟨⟨y, z⟩, ⟨hy, hz⟩, rfl⟩ := hx
  rw [Metric.mem_closedBall, dist_zero_right]
  have hy' : ‖y‖ ≤ M₁ := by
    have := hM₁ hy
    simpa [Metric.mem_closedBall, dist_zero_right] using this
  have hz' : ‖z‖ ≤ M₂ := by
    have := hM₂ hz
    simpa [Metric.mem_closedBall, dist_zero_right] using this
  have : ‖(EuclideanSpace'.prod_equiv d₁ d₂).symm (y, z)‖ ^ 2 ≤ M₁ ^ 2 + M₂ ^ 2 := by
    rw [EuclideanSpace'.norm_prod_equiv_symm]
    nlinarith [norm_nonneg y, norm_nonneg z]
  nlinarith [Real.sqrt_nonneg (M₁ ^ 2 + M₂ ^ 2),
    Real.sq_sqrt (add_nonneg (sq_nonneg M₁) (sq_nonneg M₂)),
    norm_nonneg ((EuclideanSpace'.prod_equiv d₁ d₂).symm (y, z))]

/-- Outer Jordan measure of a product is at most the product of the measures. -/
lemma Jordan_outer_measure_prod_le {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)}
    {E₂: Set (EuclideanSpace' d₂)} (hE₁: JordanMeasurable E₁) (hE₂: JordanMeasurable E₂) :
    Jordan_outer_measure (EuclideanSpace'.prod E₁ E₂) ≤ hE₁.measure * hE₂.measure := by
  have hμ₁ : 0 ≤ hE₁.measure := JordanMeasurable.nonneg hE₁
  have hμ₂ : 0 ≤ hE₂.measure := JordanMeasurable.nonneg hE₂
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ := min (1 : ℝ) (ε / (hE₁.measure + hE₂.measure + 1)) with hδdef
  have hden : (0 : ℝ) < hE₁.measure + hE₂.measure + 1 := by positivity
  have hδpos : 0 < δ := lt_min (by norm_num) (div_pos hε hden)
  have hm₁ : Jordan_outer_measure E₁ < hE₁.measure + δ := by
    rw [← hE₁.eq_outer]; exact lt_add_of_pos_right _ hδpos
  have hm₂ : Jordan_outer_measure E₂ < hE₂.measure + δ := by
    rw [← hE₂.eq_outer]; exact lt_add_of_pos_right _ hδpos
  obtain ⟨A, hA, hAE, hAμ⟩ := le_Jordan_outer hm₁ hE₁.1
  obtain ⟨B, hB, hBF, hBμ⟩ := le_Jordan_outer hm₂ hE₂.1
  have hprod_le : Jordan_outer_measure (EuclideanSpace'.prod E₁ E₂) ≤
      (hA.prod hB).measure :=
    Jordan_outer_le (hA.prod hB) (EuclideanSpace'.prod_mono hAE hBF)
  rw [IsElementary.measure_of_prod hA hB] at hprod_le
  have hA_nn : 0 ≤ hA.measure := IsElementary.measure_nonneg hA
  have hB_nn : 0 ≤ hB.measure := IsElementary.measure_nonneg hB
  have hmul : hA.measure * hB.measure ≤
      (hE₁.measure + δ) * (hE₂.measure + δ) :=
    mul_le_mul (le_of_lt hAμ) (le_of_lt hBμ) hB_nn (add_nonneg hμ₁ hδpos.le)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ * (hE₁.measure + hE₂.measure + 1) ≤ ε :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hexp : (hE₁.measure + δ) * (hE₂.measure + δ) ≤
      hE₁.measure * hE₂.measure + ε := by
    calc
      (hE₁.measure + δ) * (hE₂.measure + δ)
          = hE₁.measure * hE₂.measure + δ * (hE₁.measure + hE₂.measure + δ) := by ring
      _ ≤ hE₁.measure * hE₂.measure + δ * (hE₁.measure + hE₂.measure + 1) := by
          nlinarith [hμ₁, hμ₂, hδpos.le, hδ1]
      _ ≤ hE₁.measure * hE₂.measure + ε := by nlinarith
  linarith

/-- Inner Jordan measure of a product is at least the product of the measures. -/
lemma Jordan_inner_measure_prod_ge {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)}
    {E₂: Set (EuclideanSpace' d₂)} (hE₁: JordanMeasurable E₁) (hE₂: JordanMeasurable E₂) :
    hE₁.measure * hE₂.measure ≤ Jordan_inner_measure (EuclideanSpace'.prod E₁ E₂) := by
  have hμ₁ : 0 ≤ hE₁.measure := JordanMeasurable.nonneg hE₁
  have hμ₂ : 0 ≤ hE₂.measure := JordanMeasurable.nonneg hE₂
  have hbound := EuclideanSpace'.prod_isBounded hE₁.1 hE₂.1
  refine le_of_forall_pos_le_add fun ε hε => ?_
  by_cases h0 : hE₁.measure = 0 ∨ hE₂.measure = 0
  · have : hE₁.measure * hE₂.measure = 0 := by
      rcases h0 with h | h <;> simp [h]
    linarith [Jordan_inner_measure_nonneg (EuclideanSpace'.prod E₁ E₂)]
  · push_neg at h0
    have hpos₁ : 0 < hE₁.measure := lt_of_le_of_ne hμ₁ (Ne.symm h0.1)
    have hpos₂ : 0 < hE₂.measure := lt_of_le_of_ne hμ₂ (Ne.symm h0.2)
    have hden : (0 : ℝ) < hE₁.measure + hE₂.measure + 1 := by positivity
    set δ := min (min (hE₁.measure / 2) (hE₂.measure / 2))
      (min (1 : ℝ) (ε / (hE₁.measure + hE₂.measure + 1))) with hδdef
    have hδpos : 0 < δ :=
      lt_min (lt_min (half_pos hpos₁) (half_pos hpos₂))
        (lt_min (by norm_num) (div_pos hε hden))
    have hm₁ : hE₁.measure - δ < Jordan_inner_measure E₁ := by
      rw [← hE₁.eq_inner]; linarith
    have hm₂ : hE₂.measure - δ < Jordan_inner_measure E₂ := by
      rw [← hE₂.eq_inner]; linarith
    obtain ⟨A, hA, hAE, hAμ⟩ := Jordan_inner_le hm₁
    obtain ⟨B, hB, hBF, hBμ⟩ := Jordan_inner_le hm₂
    have hprod_ge : (hA.prod hB).measure ≤
        Jordan_inner_measure (EuclideanSpace'.prod E₁ E₂) :=
      le_Jordan_inner (hA.prod hB) (EuclideanSpace'.prod_mono hAE hBF) hbound
    rw [IsElementary.measure_of_prod hA hB] at hprod_ge
    have hA_nn : 0 ≤ hA.measure := IsElementary.measure_nonneg hA
    have hδle₁ : δ ≤ hE₁.measure / 2 := (min_le_left _ _).trans (min_le_left _ _)
    have hδle₂ : δ ≤ hE₂.measure / 2 := (min_le_left _ _).trans (min_le_right _ _)
    have hsub₂ : 0 ≤ hE₂.measure - δ := by nlinarith
    have hmul : (hE₁.measure - δ) * (hE₂.measure - δ) ≤ hA.measure * hB.measure :=
      mul_le_mul (le_of_lt hAμ) (le_of_lt hBμ) hsub₂ hA_nn
    have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    have hδε : δ * (hE₁.measure + hE₂.measure + 1) ≤ ε :=
      (le_div_iff₀ hden).mp ((min_le_right _ _).trans (min_le_right _ _))
    have : hE₁.measure * hE₂.measure ≤ (hE₁.measure - δ) * (hE₂.measure - δ) + ε := by
      calc
        hE₁.measure * hE₂.measure
            = (hE₁.measure - δ) * (hE₂.measure - δ) + δ * (hE₁.measure + hE₂.measure - δ) := by ring
        _ ≤ (hE₁.measure - δ) * (hE₂.measure - δ) + δ * (hE₁.measure + hE₂.measure + 1) := by
            nlinarith [hμ₁, hμ₂, hδpos.le, hδ1]
        _ ≤ (hE₁.measure - δ) * (hE₂.measure - δ) + ε := by nlinarith
    linarith

/-- Exercise 1.1.16 -/
theorem JordanMeasurable.prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  (hE₁: JordanMeasurable E₁) (hE₂: JordanMeasurable E₂) : JordanMeasurable (EuclideanSpace'.prod E₁ E₂) := by
  have hbound := EuclideanSpace'.prod_isBounded hE₁.1 hE₂.1
  refine ⟨hbound, le_antisymm (Jordan_inner_le_outer hbound) ?_⟩
  calc Jordan_outer_measure (EuclideanSpace'.prod E₁ E₂)
      ≤ hE₁.measure * hE₂.measure := Jordan_outer_measure_prod_le hE₁ hE₂
    _ ≤ Jordan_inner_measure (EuclideanSpace'.prod E₁ E₂) :=
        Jordan_inner_measure_prod_ge hE₁ hE₂

/-- Jordan measure is multiplicative on products: μ(E₁ × E₂) = μ(E₁) \* μ(E₂). -/
theorem JordanMeasurable.measure_of_prod {d₁ d₂:ℕ} {E₁: Set (EuclideanSpace' d₁)} {E₂: Set (EuclideanSpace' d₂)}
  (hE₁: JordanMeasurable E₁) (hE₂: JordanMeasurable E₂)
  : (hE₁.prod hE₂).measure = hE₁.measure * hE₂.measure := by
  have hp := hE₁.prod hE₂
  refine le_antisymm ?_ ?_
  · rw [JordanMeasurable.eq_outer hp]
    exact Jordan_outer_measure_prod_le hE₁ hE₂
  · rw [JordanMeasurable.eq_inner hp]
    exact Jordan_inner_measure_prod_ge hE₁ hE₂

