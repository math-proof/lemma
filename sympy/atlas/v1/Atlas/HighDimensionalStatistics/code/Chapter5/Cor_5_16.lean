/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Card
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Sequences
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.InfoTheory
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.Cor_5_13
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.Cor_5_15
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Cor_5_13
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Cor_5_15

open Real MeasureTheory InformationTheory

noncomputable section

namespace MinimaxL1Ball

/-- The `ℓ¹`-norm `|θ|_1 = ∑_i |θ_i|`. -/
def l1norm {d : ℕ} (θ : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, |θ i|

/-- The `ℓ¹`-ball of radius `R`: vectors with `|θ|_1 ≤ R`. -/
def l1Ball (d : ℕ) (R : ℝ) : Set (Fin d → ℝ) :=
  {θ | l1norm θ ≤ R}

/-- Squared Euclidean distance between two vectors in `ℝ^d`. -/
def sqDist {d : ℕ} (θ₁ θ₂ : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, (θ₁ i - θ₂ i) ^ 2

/-- A (not-necessarily measurable) estimator `ℝ^d → ℝ^d`. -/
def Estimator' (d : ℕ) := (Fin d → ℝ) → (Fin d → ℝ)

/-- `Estimator' d` is nonempty (witnessed by the identity). -/
instance {d : ℕ} : Nonempty (Estimator' d) := ⟨id⟩

/-- Subtype of measurable estimators `ℝ^d → ℝ^d`. -/
def MeasEstimator (d : ℕ) := { θhat : (Fin d → ℝ) → (Fin d → ℝ) // Measurable θhat }

/-- `MeasEstimator d` is nonempty (witnessed by the constant-zero estimator). -/
instance {d : ℕ} : Nonempty (MeasEstimator d) := ⟨⟨fun _ => 0, measurable_const⟩⟩

/-- The minimax expected risk over the `ℓ¹`-ball `B₁(R)`: infimum over measurable estimators of
the worst-case expected squared error over `θ ∈ B₁(R)`. -/
noncomputable def minimaxExpRisk_l1 {d : ℕ}
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ)) (R : ℝ) : ℝ :=
  ⨅ (θhat : MeasEstimator d),
    ⨆ θ ∈ l1Ball d R, ∫ Y, sqDist (θhat.1 Y) θ ∂(P θ)

open Classical in
/-- The constrained least squares estimator over the `ℓ¹`-ball `B₁(R)`; returns `0` if no
minimizer exists. -/
noncomputable def constrainedLSEstimator (d : ℕ) (R : ℝ) : Estimator' d :=
  fun Y => if h : ∃ θ ∈ l1Ball d R, ∀ θ' ∈ l1Ball d R, sqDist Y θ ≤ sqDist Y θ'
            then h.choose else fun _ => 0

/-- The trivial estimator `θ̂(Y) ≡ 0`. -/
def trivialEstimator (d : ℕ) : Estimator' d := fun _ => fun _ => 0

/-- The trivial estimator is measurable. -/
lemma measurable_trivialEstimator (d : ℕ) : Measurable (trivialEstimator d) :=
  measurable_const

/-- The trivial estimator bundled with its measurability proof. -/
def trivialMeasEstimator (d : ℕ) : MeasEstimator d :=
  ⟨trivialEstimator d, measurable_trivialEstimator d⟩

open Finset Filter Topology in
/-- The `ℓ¹`-ball `B₁(R)` in `ℝ^d` is compact. -/
lemma isCompact_l1Ball (d : ℕ) (R : ℝ) : IsCompact (l1Ball d R) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le
      (continuous_finset_sum _ fun i _ => continuous_abs.comp (continuous_apply i))
      continuous_const
  · rw [Metric.isBounded_iff_subset_ball 0]
    refine ⟨max R 0 + 1, fun θ hθ => ?_⟩
    simp only [Metric.mem_ball, dist_zero_right, l1Ball, Set.mem_setOf_eq, l1norm] at *
    rw [pi_norm_lt_iff (by linarith [le_max_right R 0])]
    intro i
    have h1 : |θ i| ≤ ∑ j, |θ j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (θ j)) (Finset.mem_univ i)
    calc ‖θ i‖ = |θ i| := Real.norm_eq_abs _
      _ ≤ R := le_trans h1 hθ
      _ ≤ max R 0 := le_max_left R 0
      _ < max R 0 + 1 := lt_add_one _

open Finset in
/-- The `ℓ¹`-ball `B₁(R)` is convex. -/
lemma convex_l1Ball (d : ℕ) (R : ℝ) : Convex ℝ (l1Ball d R) := by
  intro x hx y hy a b ha hb hab
  simp only [l1Ball, Set.mem_setOf_eq, l1norm] at *
  calc ∑ i, |a * x i + b * y i|
      ≤ ∑ i, (a * |x i| + b * |y i|) :=
        Finset.sum_le_sum fun i _ => (abs_add_le _ _).trans
          (by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb])
    _ = a * ∑ i, |x i| + b * ∑ i, |y i| := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ a * R + b * R :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = R := by rw [← add_mul, hab, one_mul]

open Finset in
/-- Parallelogram-style identity: `‖Y - (θ₁ + θ₂)/2‖² = (‖Y - θ₁‖² + ‖Y - θ₂‖²)/2 - ‖θ₁ - θ₂‖²/4`. -/
lemma midpoint_sqDist {d : ℕ} (Y θ₁ θ₂ : Fin d → ℝ) :
    sqDist Y (fun i => (θ₁ i + θ₂ i) / 2) =
    (sqDist Y θ₁ + sqDist Y θ₂) / 2 - sqDist θ₁ θ₂ / 4 := by
  simp only [sqDist]
  simp_rw [show ∀ i : Fin d,
      (Y i - (θ₁ i + θ₂ i) / 2) ^ 2 =
      ((Y i - θ₁ i) ^ 2 + (Y i - θ₂ i) ^ 2) / 2 - (θ₁ i - θ₂ i) ^ 2 / 4
    from fun i => by ring,
    Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_add_distrib]

open Finset in
/-- If `θ₁ ≠ θ₂`, then `sqDist θ₁ θ₂ > 0`. -/
lemma sqDist_pos_of_ne {d : ℕ} {θ₁ θ₂ : Fin d → ℝ} (h : θ₁ ≠ θ₂) :
    0 < sqDist θ₁ θ₂ := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, θ₁ i ≠ θ₂ i := by
    by_contra hall; push Not at hall; exact h (funext hall)
  exact Finset.sum_pos' (fun i _ => sq_nonneg _)
    ⟨i₀, Finset.mem_univ _, sq_pos_of_ne_zero (sub_ne_zero.mpr hi₀)⟩

/-- Two squared-distance minimizers of `Y` over a convex set `S` must coincide. -/
lemma unique_minimizer_sqDist {d : ℕ} (Y : Fin d → ℝ)
    {S : Set (Fin d → ℝ)} (hconv : Convex ℝ S)
    {θ₁ θ₂ : Fin d → ℝ} (h1 : θ₁ ∈ S) (h2 : θ₂ ∈ S)
    (hmin1 : ∀ θ' ∈ S, sqDist Y θ₁ ≤ sqDist Y θ')
    (hmin2 : ∀ θ' ∈ S, sqDist Y θ₂ ≤ sqDist Y θ') : θ₁ = θ₂ := by
  by_contra h
  let mid := fun i => (θ₁ i + θ₂ i) / 2
  have hmid : mid ∈ S := by
    have : mid = (1/2 : ℝ) • θ₁ + (1/2 : ℝ) • θ₂ := by ext i; simp [mid]; ring
    rw [this]; exact hconv h1 h2 (by norm_num) (by norm_num) (by norm_num)
  linarith [sqDist_pos_of_ne h, midpoint_sqDist Y θ₁ θ₂, hmin1 mid hmid, hmin2 mid hmid]

open Finset Filter Topology in
/-- Continuity of `sqDist` for sequences: if `Ys → Y` and `θs → θ`, then `sqDist(Ys, θs) → sqDist(Y, θ)`. -/
lemma tendsto_sqDist_of_tendsto {d : ℕ}
    {Ys : ℕ → Fin d → ℝ} {Y : Fin d → ℝ} (hY : Tendsto Ys atTop (𝓝 Y))
    {θs : ℕ → Fin d → ℝ} {θ : Fin d → ℝ} (hθ : Tendsto θs atTop (𝓝 θ)) :
    Tendsto (fun n => sqDist (Ys n) (θs n)) atTop (𝓝 (sqDist Y θ)) := by
  apply tendsto_finset_sum; intro i _
  exact ((continuous_apply i).continuousAt.tendsto.comp hY |>.sub
         ((continuous_apply i).continuousAt.tendsto.comp hθ)).pow 2

open Filter Topology in
/-- Limits of squared-distance minimizers remain minimizers. -/
lemma limit_is_minimizer_sqDist {d : ℕ} {S : Set (Fin d → ℝ)}
    {Ys : ℕ → Fin d → ℝ} {Y : Fin d → ℝ} (hY : Tendsto Ys atTop (𝓝 Y))
    {θs : ℕ → Fin d → ℝ} {θ : Fin d → ℝ} (hθ : Tendsto θs atTop (𝓝 θ))
    (hmin : ∀ n, ∀ θ' ∈ S, sqDist (Ys n) (θs n) ≤ sqDist (Ys n) θ')
    (θ' : Fin d → ℝ) (hθ' : θ' ∈ S) : sqDist Y θ ≤ sqDist Y θ' :=
  le_of_tendsto_of_tendsto
    (tendsto_sqDist_of_tendsto hY hθ)
    (tendsto_sqDist_of_tendsto hY tendsto_const_nhds)
    (Eventually.of_forall fun n => hmin n θ' hθ')

/-- The constrained `ℓ¹`-ball least squares estimator is a continuous function of the data. -/
theorem continuous_constrainedLSEstimator (d : ℕ) (R : ℝ) :
    Continuous (constrainedLSEstimator d R) := by
  open Finset Filter Topology Classical in
  by_cases hR : R < 0
  ·
    have hempty : ∀ θ : Fin d → ℝ, θ ∉ l1Ball d R := by
      intro θ hθ
      have : 0 ≤ l1norm θ := Finset.sum_nonneg (fun i _ => abs_nonneg (θ i))
      simp only [l1Ball, Set.mem_setOf_eq] at hθ
      linarith
    have hconst : constrainedLSEstimator d R = fun _ => fun _ => 0 := by
      funext Y
      simp only [constrainedLSEstimator]
      have : ¬∃ θ ∈ l1Ball d R, ∀ θ' ∈ l1Ball d R, sqDist Y θ ≤ sqDist Y θ' := by
        intro ⟨θ, hθ, _⟩; exact hempty θ hθ
      simp [dif_neg this]
    rw [hconst]; exact continuous_const
  ·
    push Not at hR
    rw [continuous_iff_seqContinuous]
    intro Ys Y hYs

    have hexists : ∀ Z : Fin d → ℝ,
        ∃ θ ∈ l1Ball d R, ∀ θ' ∈ l1Ball d R, sqDist Z θ ≤ sqDist Z θ' := by
      intro Z
      have hne : (l1Ball d R).Nonempty := ⟨0, by simp [l1Ball, l1norm, hR]⟩
      have hcont : ContinuousOn (sqDist Z) (l1Ball d R) :=
        (continuous_finset_sum _ fun i _ =>
          (continuous_const.sub (continuous_apply i)).pow 2).continuousOn
      obtain ⟨θ, hθm, hθmin⟩ := (isCompact_l1Ball d R).exists_isMinOn hne hcont
      exact ⟨θ, hθm, fun θ' hθ' => hθmin hθ'⟩

    have hval : ∀ Z : Fin d → ℝ,
        constrainedLSEstimator d R Z ∈ l1Ball d R ∧
        ∀ θ' ∈ l1Ball d R, sqDist Z (constrainedLSEstimator d R Z) ≤ sqDist Z θ' := by
      intro Z
      have h := hexists Z
      have : constrainedLSEstimator d R Z = h.choose := by
        simp only [constrainedLSEstimator]; rw [dif_pos h]
      rw [this]
      exact h.choose_spec


    apply tendsto_of_subseq_tendsto
    intro ns hns

    have hmem : ∀ n, constrainedLSEstimator d R (Ys (ns n)) ∈ l1Ball d R :=
      fun n => (hval (Ys (ns n))).1

    obtain ⟨θlim, hθlim_mem, φ, hφ_mono, hφ_tendsto⟩ :=
      (isCompact_l1Ball d R).isSeqCompact hmem

    have hYsub : Tendsto (fun n => Ys (ns (φ n))) atTop (𝓝 Y) :=
      hYs.comp (hns.comp hφ_mono.tendsto_atTop)

    have hθlim_min : ∀ θ' ∈ l1Ball d R, sqDist Y θlim ≤ sqDist Y θ' := by
      intro θ' hθ'
      apply limit_is_minimizer_sqDist hYsub hφ_tendsto
      · intro n; exact (hval (Ys (ns (φ n)))).2
      · exact hθ'


    have heq : θlim = constrainedLSEstimator d R Y :=
      unique_minimizer_sqDist Y (convex_l1Ball d R)
        hθlim_mem (hval Y).1 hθlim_min (hval Y).2

    exact ⟨φ, heq ▸ hφ_tendsto⟩

/-- Measurability of the constrained `ℓ¹`-ball least squares estimator. -/
theorem measurable_constrainedLSEstimator (d : ℕ) (R : ℝ) :
    Measurable (constrainedLSEstimator d R) :=
  (continuous_constrainedLSEstimator d R).measurable

/-- The constrained LS estimator bundled with its measurability proof. -/
noncomputable def constrainedLSMeasEstimator (d : ℕ) (R : ℝ) : MeasEstimator d :=
  ⟨constrainedLSEstimator d R, measurable_constrainedLSEstimator d R⟩
