/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/LargeDeviations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.EReal.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Structure.v1.Atlas.TheoryOfProbability.code.LargeDeviations
open Filter MeasureTheory Set
open scoped ENNReal Topology


/-- Infimal projection of a rate along the fibers of `f`. -/
noncomputable def contractedRate {X Y : Type*} (I : X → ENNReal) (f : X → Y) (y : Y) : ENNReal :=
  ⨅ x ∈ f ⁻¹' {y}, I x

/-- For any set `U`, the contracted rate on `U` matches the original rate on `f ⁻¹ U`. -/
theorem iInf_contractedRate_eq_iInf_preimage {X Y : Type*} (I : X → ENNReal) (f : X → Y)
    (U : Set Y) :
    (⨅ y ∈ U, contractedRate I f y) = ⨅ x ∈ f ⁻¹' U, I x := by
  unfold contractedRate
  apply le_antisymm
  · refine le_iInf₂ fun x hx => ?_
    refine (iInf₂_le (f x) hx).trans ?_
    exact iInf₂_le x (by simp)
  · refine le_iInf₂ fun y hy => le_iInf₂ fun x hx => ?_
    have hxU : x ∈ f ⁻¹' U := by
      simp only [mem_preimage, mem_singleton_iff] at hx ⊢
      exact hx ▸ hy
    exact iInf₂_le x hxU

/-- Coercion `ENNReal → EReal` preserves arbitrary infima. -/
theorem EReal.coe_ennreal_iInf {ι : Sort*} (g : ι → ENNReal) :
    ((⨅ i, g i : ENNReal) : EReal) = ⨅ i, (g i : EReal) := by
  apply le_antisymm
  · exact le_iInf fun i => EReal.coe_ennreal_le_coe_ennreal_iff.mpr (iInf_le g i)
  · have hnonneg : (0 : EReal) ≤ ⨅ i, (g i : EReal) :=
      le_iInf fun i => EReal.coe_ennreal_nonneg _
    have h : (⨅ i, (g i : EReal)).toENNReal ≤ ⨅ i, g i := by
      refine le_iInf fun i => ?_
      have := EReal.toENNReal_le_toENNReal (iInf_le (fun j => (g j : EReal)) i)
      rwa [EReal.toENNReal_coe] at this
    have := EReal.coe_ennreal_le_coe_ennreal_iff.mpr h
    rwa [EReal.coe_toENNReal hnonneg] at this

theorem iInf_coe_contractedRate_eq_iInf_coe_preimage {X Y : Type*} (I : X → ENNReal) (f : X → Y)
    (U : Set Y) :
    (⨅ y ∈ U, (contractedRate I f y : EReal)) =
      ⨅ x ∈ f ⁻¹' U, (I x : EReal) := by
  calc
    (⨅ y ∈ U, (contractedRate I f y : EReal))
        = ((⨅ y ∈ U, contractedRate I f y : ENNReal) : EReal) := by
          simp_rw [← EReal.coe_ennreal_iInf]
    _ = ((⨅ x ∈ f ⁻¹' U, I x : ENNReal) : EReal) := by
          rw [iInf_contractedRate_eq_iInf_preimage]
    _ = ⨅ x ∈ f ⁻¹' U, (I x : EReal) := by
          simp_rw [EReal.coe_ennreal_iInf]

/-- **Contraction principle** with Continuity and Measurability supplied separately.

Avoids `Continuous.measurable` (and thus `OpensMeasurableSpace` on the domain). This matches
Sanov's Giry-measurable empirical map on `ProbabilityMeasure`, where the weak topology and the
Giry σ-algebra need not coincide. The codomain still needs `BorelSpace` so open/closed sets are
measurable for the pushforward LDP bounds.
-/
theorem satisfiesLDP_map_of_continuous_of_measurable
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {μ : ℕ → Measure X} {I : X → ENNReal}
    (h : SatisfiesLDP μ I)
    (f : X → Y) (hfCont : Continuous f) (hfMeas : Measurable f)
    (hJ : LowerSemicontinuous (contractedRate I f)) :
    SatisfiesLDP (fun n => (μ n).map f) (contractedRate I f) := by
  refine ⟨⟨hJ⟩, ?_, ?_⟩
  · intro U hU
    have hU' : IsOpen (f ⁻¹' U) := hU.preimage hfCont
    have hmap : ∀ n, ((μ n).map f) U = μ n (f ⁻¹' U) := fun n =>
      Measure.map_apply hfMeas hU.measurableSet
    have hlb := h.lower_bound (f ⁻¹' U) hU'
    have hrate := congrArg (fun t : EReal => -t)
      (iInf_coe_contractedRate_eq_iInf_coe_preimage I f U)
    simp only [hmap, hrate] at hlb ⊢
    exact hlb
  · intro F hF
    have hF' : IsClosed (f ⁻¹' F) := hF.preimage hfCont
    have hmap : ∀ n, ((μ n).map f) F = μ n (f ⁻¹' F) := fun n =>
      Measure.map_apply hfMeas hF.measurableSet
    have hub := h.upper_bound (f ⁻¹' F) hF'
    have hrate := congrArg (fun t : EReal => -t)
      (iInf_coe_contractedRate_eq_iInf_coe_preimage I f F)
    simp only [hmap, hrate] at hub ⊢
    exact hub

/-- **Contraction principle** (continuous image) for `SatisfiesLDP`.

If `μₙ` satisfies the LDP with rate `I` and `f` is continuous, then the pushforwards
`(μₙ).map f` satisfy the LDP bounds with the contracted rate
`y ↦ ⨅_{f x = y} I x`, provided that contracted rate is lower semicontinuous.

Requires `BorelSpace` on the domain so `Continuous.measurable` applies. Prefer
`satisfiesLDP_map_of_continuous_of_measurable` when the domain is `ProbabilityMeasure`
(Giry vs weak topology).
-/
theorem satisfiesLDP_map_of_continuous
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {μ : ℕ → Measure X} {I : X → ENNReal}
    (h : SatisfiesLDP μ I)
    (f : X → Y) (hf : Continuous f)
    (hJ : LowerSemicontinuous (contractedRate I f)) :
    SatisfiesLDP (fun n => (μ n).map f) (contractedRate I f) :=
  satisfiesLDP_map_of_continuous_of_measurable h f hf hf.measurable hJ

/-- Sequential/Polish contraction: on a `SequentialSpace` domain, `SeqContinuous` upgrades to
`Continuous`, then the Borel-domain contraction applies.

Use with metrizable `ProbabilityMeasure` subclasses (Lévy–Prokhorov) once barycenter is
sequentially continuous on that subclass. Still needs `BorelSpace` on the domain; for raw
`ProbabilityMeasure` prefer `satisfiesLDP_map_of_continuous_of_measurable` plus a separate
Giry-measurability proof.
-/
theorem satisfiesLDP_map_of_seqContinuous
    {X : Type*} [TopologicalSpace X] [SequentialSpace X] [MeasurableSpace X] [BorelSpace X]
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {μ : ℕ → Measure X} {I : X → ENNReal}
    (h : SatisfiesLDP μ I)
    (f : X → Y) (hf : SeqContinuous f)
    (hJ : LowerSemicontinuous (contractedRate I f)) :
    SatisfiesLDP (fun n => (μ n).map f) (contractedRate I f) :=
  satisfiesLDP_map_of_continuous h f hf.continuous hJ

/-! ### Exponential equivalence scaffolding (Dembo–Zeitouni 4.2.13) -/

open scoped Topology EReal
open Metric

/-- Coupled exponential equivalence of maps on (possibly `n`-dependent) sample spaces:
for every `ε > 0`, `(1/n) log μ_n{dist(f n, g n) ≥ ε}` has limsup `-∞`. -/
def ExpEquivalentMaps {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    {Θ : ℕ → Type*} [∀ n, MeasurableSpace (Θ n)]
    (μ : ∀ n, Measure (Θ n)) (f g : ∀ n, Θ n → X) : Prop :=
  ∀ ε > 0,
    limsup (fun n => ((n : ℕ) : EReal)⁻¹ *
      ENNReal.log (μ n {θ | ε ≤ dist (f n θ) (g n θ)})) atTop = ⊥

/-- Family form of Dembo–Zeitouni exp-good approximation: for every `ε, δ > 0`,
eventually in the approximation parameter `R` one has
`P(dist(f, g_R) ≥ ε) ≤ exp(-δ n)` for all `n > 0`. -/
def EventuallyExpGoodApprox {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    {Θ : ℕ → Type*} [∀ n, MeasurableSpace (Θ n)]
    (μ : ∀ n, Measure (Θ n)) (f : ∀ n, Θ n → X) (g : ℝ → ∀ n, Θ n → X) : Prop :=
  ∀ ε > 0, ∀ δ > 0, ∀ᶠ R : ℝ in atTop,
    ∀ n : ℕ, 0 < n →
      (μ n).real {θ | ε ≤ dist (f n θ) (g R n θ)} ≤ Real.exp (-δ * n)

/-- `(1/n) log(a+b) ≤ (1/n) log 2 + max((1/n) log a, (1/n) log b)`. -/
theorem inv_mul_log_add_le_log_two_add_max {a b : ℝ≥0∞} {n : ℕ} (_hn : 1 ≤ n) :
    ((n : ℕ) : EReal)⁻¹ * ENNReal.log (a + b) ≤
      ((n : ℕ) : EReal)⁻¹ * ENNReal.log (2 : ℝ≥0∞) +
        max (((n : ℕ) : EReal)⁻¹ * ENNReal.log a)
          (((n : ℕ) : EReal)⁻¹ * ENNReal.log b) := by
  have hnn : 0 ≤ ((n : ℕ) : EReal) := by exact_mod_cast Nat.zero_le n
  have hinv0 : 0 ≤ ((n : ℕ) : EReal)⁻¹ := EReal.inv_nonneg_of_nonneg hnn
  have hsum : a + b ≤ 2 * max a b := by
    calc a + b ≤ max a b + max a b := add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = 2 * max a b := by rw [two_mul]
  have hlog := ENNReal.log_le_log hsum
  have htwo : ENNReal.log (2 * max a b) =
      ENNReal.log (2 : ℝ≥0∞) + ENNReal.log (max a b) := by
    rw [ENNReal.log_mul_add]
  have hmaxlog : ENNReal.log (max a b) = max (ENNReal.log a) (ENNReal.log b) := by
    by_cases h : a ≤ b
    · rw [max_eq_right h, max_eq_right (ENNReal.log_le_log h)]
    · have h' : b ≤ a := le_of_not_ge h
      rw [max_eq_left h', max_eq_left (ENNReal.log_le_log h')]
  rw [htwo, hmaxlog] at hlog
  refine (mul_le_mul_of_nonneg_left hlog hinv0).trans ?_
  have hinv_ne_top : ((n : ℕ) : EReal)⁻¹ ≠ ⊤ := by
    rw [← EReal.coe_natCast]
    exact EReal.coe_ne_top _
  have hmaxmul :
      ((n : ℕ) : EReal)⁻¹ * max (ENNReal.log a) (ENNReal.log b) =
        max (((n : ℕ) : EReal)⁻¹ * ENNReal.log a)
          (((n : ℕ) : EReal)⁻¹ * ENNReal.log b) := by
    by_cases h : ENNReal.log a ≤ ENNReal.log b
    · rw [max_eq_right h, max_eq_right (mul_le_mul_of_nonneg_left h hinv0)]
    · have h' : ENNReal.log b ≤ ENNReal.log a := le_of_not_ge h
      rw [max_eq_left h', max_eq_left (mul_le_mul_of_nonneg_left h' hinv0)]
  rw [EReal.left_distrib_of_nonneg_of_ne_top hinv0 hinv_ne_top, hmaxmul]

/-- Point in a set is either within thickening distance of the other point,
or the two points are at least `ε` apart. -/
theorem mem_cthickening_or_dist_ge {X : Type*} [PseudoMetricSpace X]
    {F : Set X} {ε : ℝ} {x y : X} (hx : x ∈ F) :
    y ∈ cthickening ε F ∨ ε ≤ dist x y := by
  by_cases h : ε ≤ dist x y
  · exact Or.inr h
  · refine Or.inl (mem_cthickening_of_dist_le y x ε F hx ?_)
    exact (dist_comm y x).symm ▸ (le_of_not_ge h)

/-- From a Chernoff real bound `μ.real s ≤ exp(-δ n)`, the EReal speed-normalized log is `≤ -δ`. -/
theorem inv_mul_log_measure_le_of_measureReal_le_exp {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsFiniteMeasure μ] (s : Set Θ) {n : ℕ} (hn : 0 < n) {δ : ℝ}
    (h : μ.real s ≤ Real.exp (-δ * n)) :
    ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ s) ≤ (-δ : EReal) := by
  have hfin : μ s ≠ ∞ := measure_ne_top μ s
  have hμ : μ s = ENNReal.ofReal (μ.real s) := (ofReal_measureReal hfin).symm
  have hexp0 : 0 ≤ Real.exp (-δ * n) := Real.exp_nonneg _
  have hlog :
      ENNReal.log (μ s) ≤ ENNReal.log (ENNReal.ofReal (Real.exp (-δ * n))) := by
    rw [hμ]
    exact ENNReal.log_le_log ((ENNReal.ofReal_le_ofReal_iff hexp0).mpr h)
  have hlogexp :
      ENNReal.log (ENNReal.ofReal (Real.exp (-δ * n))) = ((-δ * n : ℝ) : EReal) := by
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
  have hnn : 0 ≤ ((n : ℕ) : EReal) := by exact_mod_cast Nat.zero_le n
  refine (mul_le_mul_of_nonneg_left (hlog.trans (le_of_eq hlogexp))
    (EReal.inv_nonneg_of_nonneg hnn)).trans (le_of_eq ?_)
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hne : (n : ℝ) ≠ 0 := hnpos.ne'
  rw [← EReal.coe_natCast, ← EReal.coe_inv, ← EReal.coe_mul]
  exact congrArg _ (by field_simp [hne])

/-- Diagonalization: an eventually-exp-good family along `R_n → ∞` is exponentially equivalent. -/
theorem ExpEquivalentMaps_of_EventuallyExpGoodApprox_diagonal
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    {Θ : ℕ → Type*} [∀ n, MeasurableSpace (Θ n)]
    (μ : ∀ n, Measure (Θ n)) [∀ n, IsFiniteMeasure (μ n)]
    (f : ∀ n, Θ n → X) (g : ℝ → ∀ n, Θ n → X)
    (h : EventuallyExpGoodApprox μ f g)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) :
    ExpEquivalentMaps μ f (fun n => g (R n) n) := by
  intro ε hε
  refine (EReal.eq_bot_iff_forall_lt _).mpr fun M => ?_
  let δ : ℝ := max 1 (1 - M)
  have hδpos : 0 < δ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hδM : (-δ : EReal) < (M : EReal) := by
    have : 1 - M ≤ δ := le_max_right _ _
    exact EReal.coe_lt_coe_iff.mpr (by linarith : -δ < M)
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.mp (h ε hε δ hδpos)
  have hREv : ∀ᶠ n : ℕ in atTop, R₀ ≤ R n := (tendsto_atTop.mp hR) R₀
  have hev : ∀ᶠ n : ℕ in atTop,
      ((n : ℕ) : EReal)⁻¹ *
          ENNReal.log (μ n {θ | ε ≤ dist (f n θ) (g (R n) n θ)}) ≤ (-δ : EReal) := by
    filter_upwards [eventually_gt_atTop 0, hREv] with n hn0 hnR
    exact inv_mul_log_measure_le_of_measureReal_le_exp (μ n) _ hn0 (hR₀ (R n) hnR n hn0)
  exact (limsup_le_of_le (by isBoundedDefault) hev).trans_lt hδM


/-! ### Bound-only contraction + Dembo–Zeitouni 4.2.13 thickening transfer -/

/-- Continuous contraction: limsup bound only (no LSC of contracted rate). -/
theorem limsup_log_map_le_iInf_contractedRate
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {μ : ℕ → Measure X} {I : X → ENNReal}
    (h : SatisfiesLDP μ I)
    (f : X → Y) (hfCont : Continuous f) (hfMeas : Measurable f)
    {F : Set Y} (hF : IsClosed F) :
    limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (((μ n).map f) F)) atTop ≤
      - (⨅ y ∈ F, (contractedRate I f y : EReal)) := by
  have hF' : IsClosed (f ⁻¹' F) := hF.preimage hfCont
  have hmap : ∀ n, ((μ n).map f) F = μ n (f ⁻¹' F) := fun n =>
    Measure.map_apply hfMeas hF.measurableSet
  have hub := h.upper_bound (f ⁻¹' F) hF'
  have hrate := congrArg (fun t : EReal => -t)
    (iInf_coe_contractedRate_eq_iInf_coe_preimage I f F)
  simpa [hmap, hrate] using hub

/-- Continuous contraction: liminf bound only (no LSC of contracted rate). -/
theorem liminf_log_map_ge_iInf_contractedRate
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {μ : ℕ → Measure X} {I : X → ENNReal}
    (h : SatisfiesLDP μ I)
    (f : X → Y) (hfCont : Continuous f) (hfMeas : Measurable f)
    {U : Set Y} (hU : IsOpen U) :
    - (⨅ y ∈ U, (contractedRate I f y : EReal)) ≤
      liminf (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (((μ n).map f) U)) atTop := by
  have hU' : IsOpen (f ⁻¹' U) := hU.preimage hfCont
  have hmap : ∀ n, ((μ n).map f) U = μ n (f ⁻¹' U) := fun n =>
    Measure.map_apply hfMeas hU.measurableSet
  have hlb := h.lower_bound (f ⁻¹' U) hU'
  have hrate := congrArg (fun t : EReal => -t)
    (iInf_coe_contractedRate_eq_iInf_coe_preimage I f U)
  simpa [hmap, hrate] using hlb

/-- Preimage inclusion for closed sets under metrically close maps. -/
theorem preimage_subset_cthickening_union_dist
    {X Θ : Type*} [PseudoMetricSpace X] {F : Set X} {ε : ℝ}
    (f g : Θ → X) :
    f ⁻¹' F ⊆ g ⁻¹' (cthickening ε F) ∪ {θ | ε ≤ dist (f θ) (g θ)} := by
  intro θ hθ
  cases mem_cthickening_or_dist_ge (x := f θ) (y := g θ) (F := F) (ε := ε) hθ with
  | inl hmem => exact Or.inl hmem
  | inr hdist => exact Or.inr hdist

/-- `(1/n) log 2 → 0` in `EReal`. -/
theorem tendsto_inv_mul_log_two_nhds_zero :
    Tendsto (fun n : ℕ => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (2 : ℝ≥0∞)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hlog : ENNReal.log (2 : ℝ≥0∞) = ((Real.log 2 : ℝ) : EReal) := by
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := (ENNReal.ofReal_natCast 2).symm
    rw [h2, ENNReal.log_ofReal_of_pos (by norm_num : (0 : ℝ) < 2)]
  simp only [hlog]
  have hmul : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * Real.log 2) atTop (𝓝 0) := by
    simpa [mul_comm] using hinv.mul_const (Real.log 2)
  have hcoe := EReal.tendsto_coe.mpr hmul
  convert hcoe using 1
  · funext n
    rw [← EReal.coe_natCast, ← EReal.coe_inv, ← EReal.coe_mul]
  · simp

/-- Filter form: limsup of `(1/n) log(a_n+b_n)` ≤ max of the two limsups. -/
theorem limsup_inv_mul_log_add_le_max {a b : ℕ → ℝ≥0∞} :
    limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (a n + b n)) atTop ≤
      max (limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (a n)) atTop)
        (limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (b n)) atTop) := by
  set ua := fun n : ℕ => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (a n)
  set ub := fun n : ℕ => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (b n)
  set u2 := fun n : ℕ => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (2 : ℝ≥0∞)
  have hle : ∀ᶠ n : ℕ in atTop,
      ((n : ℕ) : EReal)⁻¹ * ENNReal.log (a n + b n) ≤ u2 n + max (ua n) (ub n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa [ua, ub, u2] using
      inv_mul_log_add_le_log_two_add_max (a := a n) (b := b n) hn
  refine (limsup_le_limsup hle).trans ?_
  have hmax :
      limsup (fun n => max (ua n) (ub n)) atTop =
        max (limsup ua atTop) (limsup ub atTop) := limsup_max
  have h0 : limsup u2 atTop = 0 := tendsto_inv_mul_log_two_nhds_zero.limsup_eq
  have hsum :
      limsup (fun n => u2 n + max (ua n) (ub n)) atTop ≤
        limsup u2 atTop + limsup (fun n => max (ua n) (ub n)) atTop := by
    change limsup (u2 + fun n => max (ua n) (ub n)) atTop ≤ _
    exact EReal.limsup_add_le
      (Or.inl (by rw [h0]; exact EReal.zero_ne_bot))
      (Or.inl (by rw [h0]; exact EReal.zero_ne_top))
  refine hsum.trans ?_
  rw [h0, hmax, zero_add]

/-- Exp-equivalence transfers closed-set limsup through thickenings (DZ 4.2.13 half). -/
theorem limsup_log_map_le_iInf_cthickening_of_ExpEquivalentMaps
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {Θ : ℕ → Type*} [∀ n, MeasurableSpace (Θ n)]
    (μ : ∀ n, Measure (Θ n)) [∀ n, IsFiniteMeasure (μ n)]
    (f g : ∀ n, Θ n → X)
    (hfMeas : ∀ n, Measurable (f n)) (hgMeas : ∀ n, Measurable (g n))
    (hexp : ExpEquivalentMaps μ f g)
    {F : Set X} (hF : IsClosed F) :
    limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log ((μ n).map (f n) F)) atTop ≤
      ⨅ ε : {ε : ℝ // 0 < ε},
        limsup (fun n => ((n : ℕ) : EReal)⁻¹ *
          ENNReal.log ((μ n).map (g n) (cthickening ε.1 F))) atTop := by
  refine le_iInf fun ε => ?_
  have hε : 0 < ε.1 := ε.2
  have hsubset : ∀ n,
      (μ n).map (f n) F ≤
        (μ n).map (g n) (cthickening ε.1 F) +
          μ n {θ | ε.1 ≤ dist (f n θ) (g n θ)} := by
    intro n
    have hmeasF : MeasurableSet F := hF.measurableSet
    have hmeasT : MeasurableSet (cthickening ε.1 F) := isClosed_cthickening.measurableSet
    rw [Measure.map_apply (hfMeas n) hmeasF, Measure.map_apply (hgMeas n) hmeasT]
    exact (measure_mono
      (preimage_subset_cthickening_union_dist (f n) (g n))).trans (measure_union_le _ _)
  have hle : ∀ n,
      ((n : ℕ) : EReal)⁻¹ * ENNReal.log ((μ n).map (f n) F) ≤
        ((n : ℕ) : EReal)⁻¹ * ENNReal.log
          ((μ n).map (g n) (cthickening ε.1 F) +
            μ n {θ | ε.1 ≤ dist (f n θ) (g n θ)}) := fun n =>
    mul_le_mul_of_nonneg_left (ENNReal.log_le_log (hsubset n))
      (EReal.inv_nonneg_of_nonneg (by exact_mod_cast Nat.zero_le n))
  refine (limsup_le_limsup (Eventually.of_forall hle)).trans ?_
  refine (limsup_inv_mul_log_add_le_max
    (a := fun n => (μ n).map (g n) (cthickening ε.1 F))
    (b := fun n => μ n {θ | ε.1 ≤ dist (f n θ) (g n θ)})).trans ?_
  have hbot :
      limsup (fun n => ((n : ℕ) : EReal)⁻¹ *
        ENNReal.log (μ n {θ | ε.1 ≤ dist (f n θ) (g n θ)})) atTop = ⊥ :=
    hexp ε.1 hε
  rw [hbot, max_eq_left bot_le]

/-- Compact finite sublevels: `{x | I x ≤ ofReal a}` compact for every real `a`. -/
def HasCompactFiniteLevelSets {X : Type*} [TopologicalSpace X] (I : X → ENNReal) : Prop :=
  ∀ a : ℝ, IsCompact {x : X | I x ≤ ENNReal.ofReal a}

/-- Always `F ⊆ cthickening ε F`, so closed-set infima decrease under thickening. -/
theorem iInf_cthickening_le_iInf {X : Type*} [PseudoMetricSpace X]
    (I : X → ENNReal) (F : Set X) (ε : ℝ) :
    (⨅ x ∈ cthickening ε F, I x) ≤ ⨅ x ∈ F, I x :=
  iInf₂_mono' fun x hx => ⟨x, self_subset_cthickening F hx, le_rfl⟩

/-- Nearly-minimizer on a thickening: `inf ≤ ofReal A` yields a point with rate `≤ ofReal (A+1)`. -/
theorem exists_mem_cthickening_le_ofReal_add_one
    {X : Type*} [PseudoMetricSpace X]
    (I : X → ENNReal) {F : Set X} {ε A : ℝ}
    (hA : 0 ≤ A)
    (hinf : ⨅ x ∈ cthickening ε F, I x ≤ ENNReal.ofReal A) :
    ∃ x ∈ cthickening ε F, I x ≤ ENNReal.ofReal (A + 1) := by
  by_contra hnone
  push Not at hnone
  have hbig : ∀ x ∈ cthickening ε F, ENNReal.ofReal (A + 1) < I x := hnone
  have hle : ENNReal.ofReal (A + 1) ≤ ⨅ x ∈ cthickening ε F, I x :=
    le_iInf₂ fun x hx => (hbig x hx).le
  have hlt : ENNReal.ofReal A < ENNReal.ofReal (A + 1) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < A + 1)).2 (by linarith)
  exact (not_lt_of_ge (hle.trans hinf)) hlt


/-! ### Thickening recovery of set-infima (Dembo–Zeitouni Lemma 4.1.6) -/

/-- Nearly-minimizer on a thickening with arbitrary additive slack. -/
theorem exists_mem_cthickening_le_ofReal_add
    {X : Type*} [PseudoMetricSpace X]
    (I : X → ENNReal) {F : Set X} {ε A δ : ℝ}
    (hA : 0 ≤ A) (hδ : 0 < δ)
    (hinf : ⨅ x ∈ cthickening ε F, I x ≤ ENNReal.ofReal A) :
    ∃ x ∈ cthickening ε F, I x ≤ ENNReal.ofReal (A + δ) := by
  by_contra hnone
  push Not at hnone
  have hbig : ∀ x ∈ cthickening ε F, ENNReal.ofReal (A + δ) < I x := hnone
  have hle : ENNReal.ofReal (A + δ) ≤ ⨅ x ∈ cthickening ε F, I x :=
    le_iInf₂ fun x hx => (hbig x hx).le
  have hlt : ENNReal.ofReal A < ENNReal.ofReal (A + δ) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < A + δ)).2 (by linarith)
  exact (not_lt_of_ge (hle.trans hinf)) hlt

/-- Closed-set thickening recovery: for an LSC rate with compact finite sublevels,
`inf_F I ≤ ⨆_{ε>0} inf_{F^ε} I`. Combined with `iInf_cthickening_le_iInf` this yields
equality (Dembo–Zeitouni 4.1.6). -/
theorem iInf_le_iSup_iInf_cthickening
    {X : Type*} [PseudoMetricSpace X]
    (I : X → ENNReal) (hI : LowerSemicontinuous I)
    (hK : HasCompactFiniteLevelSets I)
    {F : Set X} (hF : IsClosed F) :
    (⨅ x ∈ F, I x) ≤ ⨆ ε : {ε : ℝ // 0 < ε}, ⨅ x ∈ cthickening ε.1 F, I x := by
  classical
  set α : ENNReal := ⨆ ε : {ε : ℝ // 0 < ε}, ⨅ x ∈ cthickening ε.1 F, I x
  by_cases htop : α = ∞
  · exact htop ▸ le_top
  · have hα_ofReal : α = ENNReal.ofReal α.toReal := (ENNReal.ofReal_toReal htop).symm
    have hA0 : 0 ≤ α.toReal := ENNReal.toReal_nonneg
    let εn : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)⁻¹
    have hεpos : ∀ n, 0 < εn n := fun n =>
      inv_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos n))
    have hinf_le : ∀ n, ⨅ x ∈ cthickening (εn n) F, I x ≤ α := fun n =>
      le_iSup
        (fun ε : {ε : ℝ // 0 < ε} => ⨅ x ∈ cthickening ε.1 F, I x)
        ⟨εn n, hεpos n⟩
    have hnear : ∀ n, ∃ x ∈ cthickening (εn n) F,
        I x ≤ ENNReal.ofReal (α.toReal + εn n) := fun n =>
      exists_mem_cthickening_le_ofReal_add I hA0 (hεpos n)
        ((hinf_le n).trans_eq hα_ofReal)
    choose xn hxn_mem hxn_I using hnear
    have hlevel : ∀ n, xn n ∈ {x : X | I x ≤ ENNReal.ofReal (α.toReal + 1)} := by
      intro n
      have hεle : εn n ≤ (1 : ℝ) :=
        inv_le_one_of_one_le₀ (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n)))
      exact (hxn_I n).trans
        (ENNReal.ofReal_le_ofReal (add_le_add (le_refl α.toReal) hεle))
    obtain ⟨z, _hz_mem, φ, hφ, hconv⟩ :=
      (hK (α.toReal + 1)).tendsto_subseq hlevel
    have hinfE : Tendsto (fun n => Metric.infEDist (xn (φ n)) F) atTop
        (𝓝 (Metric.infEDist z F)) :=
      (Metric.continuous_infEDist.tendsto _).comp hconv
    have hεnφ : Tendsto (fun n => εn (φ n)) atTop (𝓝 0) := by
      change Tendsto (fun n => ((φ n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0)
      refine tendsto_inv_atTop_zero.comp ?_
      have hφ' : Tendsto (fun n => φ n + 1) atTop atTop :=
        (tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop
      exact tendsto_natCast_atTop_iff.2 hφ'
    have hsqueeze :
        Tendsto (fun n => Metric.infEDist (xn (φ n)) F) atTop (𝓝 0) := by
      have hof : Tendsto (fun n => ENNReal.ofReal (εn (φ n))) atTop (𝓝 0) := by
        rw [← ENNReal.ofReal_zero]
        exact (ENNReal.continuous_ofReal.tendsto 0).comp hεnφ
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hof
        (fun _ => bot_le) ?_
      intro n
      exact (mem_cthickening_iff).1 (hxn_mem (φ n))
    have hz0 : Metric.infEDist z F = 0 := tendsto_nhds_unique hinfE hsqueeze
    have hzF : z ∈ F := (Metric.mem_iff_infEDist_zero_of_closed hF).2 hz0
    have hls : I z ≤ liminf (fun n => I (xn (φ n))) atTop := by
      have hnhds : I z ≤ liminf I (𝓝 z) := hI.le_liminf z
      have hseq : liminf I (𝓝 z) ≤ liminf (fun n => I (xn (φ n))) atTop :=
        hconv.liminf_le_liminf_comp
      exact hnhds.trans hseq
    have hlim_ofReal :
        Tendsto (fun n => ENNReal.ofReal (α.toReal + εn (φ n))) atTop (𝓝 α) := by
      have hsum : Tendsto (fun n => α.toReal + εn (φ n)) atTop (𝓝 α.toReal) := by
        simpa [add_zero] using Tendsto.const_add α.toReal hεnφ
      have h' : Tendsto (fun n => ENNReal.ofReal (α.toReal + εn (φ n))) atTop
          (𝓝 (ENNReal.ofReal α.toReal)) :=
        (ENNReal.continuous_ofReal.tendsto α.toReal).comp hsum
      rwa [← hα_ofReal] at h'
    have hliminf_I : liminf (fun n => I (xn (φ n))) atTop ≤ α := by
      have hle' :
          liminf (fun n => I (xn (φ n))) atTop ≤
            liminf (fun n => ENNReal.ofReal (α.toReal + εn (φ n))) atTop :=
        liminf_le_liminf (Eventually.of_forall fun n => hxn_I (φ n))
      simpa [hlim_ofReal.liminf_eq] using hle'
    exact (iInf₂_le z hzF).trans (hls.trans hliminf_I)

/-- Equality form of thickening recovery for LSC rates with compact finite sublevels. -/
theorem iSup_iInf_cthickening_eq_iInf
    {X : Type*} [PseudoMetricSpace X]
    (I : X → ENNReal) (hI : LowerSemicontinuous I)
    (hK : HasCompactFiniteLevelSets I)
    {F : Set X} (hF : IsClosed F) :
    (⨆ ε : {ε : ℝ // 0 < ε}, ⨅ x ∈ cthickening ε.1 F, I x) = ⨅ x ∈ F, I x :=
  le_antisymm
    (iSup_le fun ε => iInf_cthickening_le_iInf I F ε.1)
    (iInf_le_iSup_iInf_cthickening I hI hK hF)






/-! ### Exp-equivalence transfers full LDP (Dembo–Zeitouni 4.2.13) -/

/-- Coercion `ENNReal → EReal` preserves nonempty-indexed suprema. -/
theorem EReal.coe_ennreal_iSup {ι : Sort*} [Nonempty ι] (g : ι → ENNReal) :
    ((⨆ i, g i : ENNReal) : EReal) = ⨆ i, (g i : EReal) := by
  refine le_antisymm ?_ ?_
  · inhabit ι
    have hn : (0 : EReal) ≤ ⨆ i, (g i : EReal) :=
      (EReal.coe_ennreal_nonneg (g default)).trans (le_iSup (fun i => (g i : EReal)) default)
    have hle : ⨆ i, g i ≤ (⨆ i, (g i : EReal)).toENNReal :=
      iSup_le fun i => by
        rw [← EReal.toENNReal_coe]
        exact EReal.toENNReal_le_toENNReal (le_iSup (fun j => (g j : EReal)) i)
    exact (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hle).trans_eq (EReal.coe_toENNReal hn)
  · exact Monotone.le_map_iSup (fun _ _ h => EReal.coe_ennreal_le_coe_ennreal_iff.mpr h)

/-- Negation swaps `iSup` and `iInf` on `EReal`. -/
theorem EReal.neg_iSup_eq_iInf_neg {ι : Sort*} (g : ι → EReal) :
    -(⨆ i, g i) = ⨅ i, -g i := by
  refine le_antisymm ?_ ?_
  · exact le_iInf fun i => neg_le_neg (le_iSup g i)
  · rw [le_neg]
    exact iSup_le fun i => le_neg.mpr (iInf_le (fun j => -g j) i)

/-- EReal wire: `⨅_ε (-inf_{F^ε} I) = -inf_F I` via thickening recovery. -/
theorem iInf_neg_iInf_cthickening_eq_neg_iInf
    {X : Type*} [PseudoMetricSpace X]
    (I : X → ENNReal) (hI : LowerSemicontinuous I)
    (hK : HasCompactFiniteLevelSets I)
    {F : Set X} (hF : IsClosed F) :
    (⨅ ε : {ε : ℝ // 0 < ε},
        (-(⨅ x ∈ cthickening ε.1 F, (I x : EReal)) : EReal)) =
      - (⨅ x ∈ F, (I x : EReal)) := by
  set a : {ε : ℝ // 0 < ε} → ENNReal := fun ε => ⨅ x ∈ cthickening ε.1 F, I x
  have hrec : ⨆ ε, a ε = ⨅ x ∈ F, I x := iSup_iInf_cthickening_eq_iInf I hI hK hF
  have _hnonempty : Nonempty {ε : ℝ // 0 < ε} := ⟨⟨1, one_pos⟩⟩
  calc
    (⨅ ε : {ε : ℝ // 0 < ε}, (-(⨅ x ∈ cthickening ε.1 F, (I x : EReal)) : EReal))
        = ⨅ ε, (-(a ε : EReal)) := by
          simp only [a, ← EReal.coe_ennreal_iInf]
    _ = - (⨆ ε, (a ε : EReal)) := (EReal.neg_iSup_eq_iInf_neg (fun ε => (a ε : EReal))).symm
    _ = - ((⨆ ε, a ε : ENNReal) : EReal) := by rw [← EReal.coe_ennreal_iSup]
    _ = - ((⨅ x ∈ F, I x : ENNReal) : EReal) := by rw [hrec]
    _ = - (⨅ x ∈ F, (I x : EReal)) := by rw [EReal.coe_ennreal_iInf]

/-- Closed-set limsup under exp-equivalence recovers the good rate on `F`. -/
theorem limsup_log_map_le_neg_iInf_of_ExpEquivalentMaps
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {Θ : ℕ → Type*} [∀ n, MeasurableSpace (Θ n)]
    (μ : ∀ n, Measure (Θ n)) [∀ n, IsFiniteMeasure (μ n)]
    (f g : ∀ n, Θ n → X)
    (hfMeas : ∀ n, Measurable (f n)) (hgMeas : ∀ n, Measurable (g n))
    (hexp : ExpEquivalentMaps μ f g)
    (I : X → ENNReal) (hI : LowerSemicontinuous I)
    (hK : HasCompactFiniteLevelSets I)
    (hup : ∀ (F : Set X), IsClosed F →
      limsup (fun n => ((n : ℕ) : EReal)⁻¹ *
        ENNReal.log ((μ n).map (g n) F)) atTop ≤
          - (⨅ x ∈ F, (I x : EReal)))
    {F : Set X} (hF : IsClosed F) :
    limsup (fun n => ((n : ℕ) : EReal)⁻¹ *
      ENNReal.log ((μ n).map (f n) F)) atTop ≤
        - (⨅ x ∈ F, (I x : EReal)) := by
  have hthick := limsup_log_map_le_iInf_cthickening_of_ExpEquivalentMaps
    μ f g hfMeas hgMeas hexp hF
  refine hthick.trans ?_
  have hεbound : ∀ ε : {ε : ℝ // 0 < ε},
      limsup (fun n => ((n : ℕ) : EReal)⁻¹ *
        ENNReal.log ((μ n).map (g n) (cthickening ε.1 F))) atTop ≤
          - (⨅ x ∈ cthickening ε.1 F, (I x : EReal)) :=
    fun ε => hup _ isClosed_cthickening
  refine (iInf_mono hεbound).trans (le_of_eq ?_)
  exact iInf_neg_iInf_cthickening_eq_neg_iInf I hI hK hF

/-- When `limsup v = ⊥`, one has `liminf (max u v) ≤ liminf u`. -/
theorem liminf_max_le_of_limsup_eq_bot {u v : ℕ → EReal}
    (hv : limsup v atTop = ⊥) :
    liminf (fun n => max (u n) (v n)) atTop ≤ liminf u atTop := by
  have hle : liminf u atTop ≤ liminf (fun n => max (u n) (v n)) atTop :=
    liminf_le_liminf (Eventually.of_forall fun n => le_max_left (u n) (v n))
  -- reverse via: for all M, limsup v ≤ M → eventually v ≤ M, take M = liminf u
  have hlim : limsup v atTop ≤ liminf u atTop := hv ▸ bot_le
  have hev : ∀ᶠ n in atTop, v n ≤ liminf u atTop := by
    -- limsup = ⊥ implies ∀ y, eventually v < y (if y ≠ ⊥), or use eq_bot_iff
    refine (EReal.eq_bot_iff_forall_lt.mp hv (liminf u atTop)).mono fun n hn => hn.le
  have hmax : ∀ᶠ n in atTop, max (u n) (v n) ≤ max (u n) (liminf u atTop) := by
    filter_upwards [hev] with n hn
    exact max_le_max le_rfl hn
  refine (liminf_le_liminf hmax).trans ?_
  have hconst :
      liminf (fun n => max (u n) (liminf u atTop)) atTop =
        max (liminf u atTop) (liminf u atTop) := by
    have := liminf_const (f := atTop) (a := liminf u atTop)
    -- max(u n, L) has liminf = max(liminf u, L) via limsup_max dual? use identity
    -- max(x,L) = x ⊔ L, and liminf (u ⊔ const L) = liminf u ⊔ L = max(liminf u, L)
    simpa [sup_eq_max] using (sup_liminf (liminf u atTop) (u := u)).symm
  rw [hconst, max_self]

/-- If limsup of `(1/n)log b` is `-∞`, then liminf `(1/n)log(a+b) ≤` liminf `(1/n)log a`. -/
theorem liminf_inv_mul_log_add_le_of_limsup_eq_bot
    {a b : ℕ → ℝ≥0∞}
    (hb : limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (b n)) atTop = ⊥) :
    liminf (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (a n + b n)) atTop ≤
      liminf (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (a n)) atTop := by
  set ua := fun n : ℕ => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (a n)
  set ub := fun n : ℕ => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (b n)
  set u2 := fun n : ℕ => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (2 : ℝ≥0∞)
  have hmaxbound : ∀ᶠ n in atTop,
      ((n : ℕ) : EReal)⁻¹ * ENNReal.log (a n + b n) ≤ u2 n + max (ua n) (ub n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa [ua, ub, u2] using inv_mul_log_add_le_log_two_add_max (a := a n) (b := b n) hn
  refine (liminf_le_liminf hmaxbound).trans ?_
  have hu2s : limsup u2 atTop = 0 := tendsto_inv_mul_log_two_nhds_zero.limsup_eq
  have hsum :
      liminf (fun n => u2 n + max (ua n) (ub n)) atTop ≤
        limsup u2 atTop + liminf (fun n => max (ua n) (ub n)) atTop := by
    change liminf (u2 + fun n => max (ua n) (ub n)) atTop ≤ _
    exact EReal.liminf_add_le
      (Or.inl (by rw [hu2s]; exact EReal.zero_ne_bot))
      (Or.inl (by rw [hu2s]; exact EReal.zero_ne_top))
  refine hsum.trans ?_
  rw [hu2s, zero_add]
  exact liminf_max_le_of_limsup_eq_bot (u := ua) (v := ub) hb

/-- Open lower bound at a point via balls under exponential equivalence. -/
theorem liminf_log_map_ge_neg_rate_of_ExpEquivalentMaps
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {Θ : ℕ → Type*} [∀ n, MeasurableSpace (Θ n)]
    (μ : ∀ n, Measure (Θ n)) [∀ n, IsFiniteMeasure (μ n)]
    (f g : ∀ n, Θ n → X)
    (hfMeas : ∀ n, Measurable (f n)) (hgMeas : ∀ n, Measurable (g n))
    (hexp : ExpEquivalentMaps μ f g)
    (I : X → ENNReal)
    (hlow : ∀ (U : Set X), IsOpen U →
      - (⨅ x ∈ U, (I x : EReal)) ≤
        liminf (fun n => ((n : ℕ) : EReal)⁻¹ *
          ENNReal.log ((μ n).map (g n) U)) atTop)
    {U : Set X} (hU : IsOpen U) (x : X) (hx : x ∈ U) :
    - (I x : EReal) ≤
      liminf (fun n => ((n : ℕ) : EReal)⁻¹ *
        ENNReal.log ((μ n).map (f n) U)) atTop := by
  obtain ⟨δ, hδpos, hball⟩ : ∃ δ > 0, Metric.ball x δ ⊆ U :=
    Metric.isOpen_iff.mp hU x hx
  set δ2 : ℝ := δ / 2
  have hδ2 : 0 < δ2 := half_pos hδpos
  have hball2 : Metric.ball x δ2 ⊆ U :=
    (Metric.ball_subset_ball (by linarith : δ2 ≤ δ)).trans hball
  have hsubset : ∀ n,
      (μ n).map (g n) (Metric.ball x δ2) ≤
        (μ n).map (f n) U + μ n {θ | δ2 ≤ dist (f n θ) (g n θ)} := by
    intro n
    have hmeasB : MeasurableSet (Metric.ball x δ2) := Metric.isOpen_ball.measurableSet
    have hmeasU : MeasurableSet U := hU.measurableSet
    rw [Measure.map_apply (hgMeas n) hmeasB, Measure.map_apply (hfMeas n) hmeasU]
    refine (measure_mono ?_).trans (measure_union_le _ _)
    intro θ hθ
    by_cases hd : δ2 ≤ dist (f n θ) (g n θ)
    · exact Or.inr hd
    · refine Or.inl (hball2 ?_)
      have hg : dist (g n θ) x < δ2 := Metric.mem_ball.mp hθ
      have hlt : dist (f n θ) (g n θ) < δ2 := lt_of_not_ge hd
      have htri : dist (f n θ) x ≤ dist (f n θ) (g n θ) + dist (g n θ) x :=
        dist_triangle _ _ _
      exact Metric.mem_ball.mpr (lt_of_le_of_lt htri (by linarith))
  have hle : ∀ n,
      ((n : ℕ) : EReal)⁻¹ * ENNReal.log ((μ n).map (g n) (Metric.ball x δ2)) ≤
        ((n : ℕ) : EReal)⁻¹ * ENNReal.log
          ((μ n).map (f n) U + μ n {θ | δ2 ≤ dist (f n θ) (g n θ)}) := fun n =>
    mul_le_mul_of_nonneg_left (ENNReal.log_le_log (hsubset n))
      (EReal.inv_nonneg_of_nonneg (by exact_mod_cast Nat.zero_le n))
  have hbot :
      limsup (fun n => ((n : ℕ) : EReal)⁻¹ *
        ENNReal.log (μ n {θ | δ2 ≤ dist (f n θ) (g n θ)})) atTop = ⊥ :=
    hexp δ2 hδ2
  have hstep := liminf_le_liminf (Eventually.of_forall hle)
  have hadd := liminf_inv_mul_log_add_le_of_limsup_eq_bot
    (a := fun n => (μ n).map (f n) U)
    (b := fun n => μ n {θ | δ2 ≤ dist (f n θ) (g n θ)}) hbot
  have hge_ball :
      - (⨅ y ∈ Metric.ball x δ2, (I y : EReal)) ≤
        liminf (fun n => ((n : ℕ) : EReal)⁻¹ *
          ENNReal.log ((μ n).map (g n) (Metric.ball x δ2))) atTop :=
    hlow _ Metric.isOpen_ball
  have hIx : - (I x : EReal) ≤ - (⨅ y ∈ Metric.ball x δ2, (I y : EReal)) :=
    neg_le_neg (iInf₂_le x (Metric.mem_ball_self hδ2))
  exact hIx.trans (hge_ball.trans (hstep.trans hadd))

/-- Full LDP transfer along exponentially equivalent maps with a common good rate
(Dembo–Zeitouni 4.2.13). -/
theorem satisfiesLDP_of_ExpEquivalentMaps
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {Θ : ℕ → Type*} [∀ n, MeasurableSpace (Θ n)]
    (μ : ∀ n, Measure (Θ n)) [∀ n, IsFiniteMeasure (μ n)]
    (f g : ∀ n, Θ n → X)
    (hfMeas : ∀ n, Measurable (f n)) (hgMeas : ∀ n, Measurable (g n))
    (hexp : ExpEquivalentMaps μ f g)
    (I : X → ENNReal)
    (hLDP : SatisfiesLDP (fun n => (μ n).map (g n)) I)
    (hK : HasCompactFiniteLevelSets I) :
    SatisfiesLDP (fun n => (μ n).map (f n)) I := by
  refine ⟨hLDP.isRateFunction, ?_, ?_⟩
  · intro U hU
    have hx : ∀ x ∈ U,
        - (I x : EReal) ≤
          liminf (fun n => ((n : ℕ) : EReal)⁻¹ *
            ENNReal.log ((μ n).map (f n) U)) atTop :=
      fun x hx => liminf_log_map_ge_neg_rate_of_ExpEquivalentMaps
        μ f g hfMeas hgMeas hexp I hLDP.lower_bound hU x hx
    have hrew :
        - (⨅ x ∈ U, (I x : EReal)) = ⨆ x : U, - (I x.1 : EReal) := by
      change - (⨅ x : U, (I x.1 : EReal)) = ⨆ x : U, - (I x.1 : EReal)
      exact (EReal.neg_iSup_eq_iInf_neg (fun x : U => (I x.1 : EReal))).symm
    rw [hrew]
    exact iSup_le fun x : U => hx x.1 x.2
  · intro F hF
    exact limsup_log_map_le_neg_iInf_of_ExpEquivalentMaps
      μ f g hfMeas hgMeas hexp I hLDP.isRateFunction.lowerSemicontinuous hK
      hLDP.upper_bound hF

/-! ### Γ-liminf predicates (toward Dembo–Zeitouni 4.2.16) -/

/-- Sequential Γ-liminf of rates `I n` toward `J`. -/
def GammaLiminf {X : Type*} [TopologicalSpace X]
    (I : ℕ → X → ENNReal) (J : X → ENNReal) : Prop :=
  ∀ y : X, ∀ yseq : ℕ → X, Tendsto yseq atTop (𝓝 y) →
    J y ≤ liminf (fun n => I n (yseq n)) atTop

/-- Real-parameter Γ-liminf along every `R_n → ∞` diagonal. -/
def GammaLiminfReal {X : Type*} [TopologicalSpace X]
    (I : ℝ → X → ENNReal) (J : X → ENNReal) : Prop :=
  ∀ y : X, ∀ (R : ℕ → ℝ), Tendsto R atTop atTop →
    ∀ yseq : ℕ → X, Tendsto yseq atTop (𝓝 y) →
      J y ≤ liminf (fun n => I (R n) (yseq n)) atTop
