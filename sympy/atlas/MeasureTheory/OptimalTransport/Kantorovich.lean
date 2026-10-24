/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.Order.Compact

section
open MeasureTheory
open scoped BoundedContinuousFunction CompactlySupported ENNReal

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/-!
# Kantorovich duality on compact metric spaces

Strong Kantorovich duality on products of nonempty compact
metric Borel probability spaces with continuous cost.
-/

/-- Coupling of `μ` and `ν`: prob. measure on `X × Y` with marginals `μ`, `ν`. -/
def IsCoupling {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (π : ProbabilityMeasure (X × Y)) : Prop :=
  (μ : Measure X) = (π : Measure (X × Y)).map Prod.fst ∧
    (ν : Measure Y) = (π : Measure (X × Y)).map Prod.snd

/-- Values of `∫ c dπ` over couplings `π` of `μ`, `ν`. -/
def primalValues {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) : Set ℝ :=
  {r : ℝ | ∃ π : ProbabilityMeasure (X × Y),
    IsCoupling μ ν π ∧ r = ∫ p, c p ∂(π : Measure (X × Y))}

/-- Dual feasibility: continuous `φ`, `ψ` with `φ x + ψ y ≤ c (x,y)`. -/
def DualFeasible {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (c : X × Y → ℝ) (φ : X → ℝ) (ψ : Y → ℝ) : Prop :=
  Continuous φ ∧ Continuous ψ ∧ ∀ x y, φ x + ψ y ≤ c (x, y)

/-- A continuous real function on a compact space is integrable w.r.t. any finite measure. -/
private lemma integrable_continuous_compact
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (f : X → ℝ) (hf : Continuous f) (μ : Measure X) [IsFiniteMeasure μ] :
    Integrable f μ := by
  rw [← integrableOn_univ]
  exact ContinuousOn.integrableOn_compact isCompact_univ hf.continuousOn

/-- Weak duality: any dual-feasible value is below any primal (coupling) value. -/
private lemma dual_le_primal_of_isCoupling
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) (hc : Continuous c) (φ : X → ℝ) (ψ : Y → ℝ)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (hle : ∀ x y, φ x + ψ y ≤ c (x, y))
    (π : ProbabilityMeasure (X × Y)) (hπ : IsCoupling μ ν π) :
    (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)
      ≤ ∫ p, c p ∂(π : Measure (X × Y)) := by
  obtain ⟨hμ, hν⟩ := hπ
  have hφπ : Integrable (fun p : X × Y => φ p.1) (π : Measure (X × Y)) :=
    integrable_continuous_compact _ (hφ.comp continuous_fst) _
  have hψπ : Integrable (fun p : X × Y => ψ p.2) (π : Measure (X × Y)) :=
    integrable_continuous_compact _ (hψ.comp continuous_snd) _
  have hcπ : Integrable c (π : Measure (X × Y)) :=
    integrable_continuous_compact _ hc _
  have eφ : (∫ x, φ x ∂(μ : Measure X))
      = ∫ p : X × Y, φ p.1 ∂(π : Measure (X × Y)) := by
    rw [hμ, integral_map measurable_fst.aemeasurable hφ.aestronglyMeasurable]
  have eψ : (∫ y, ψ y ∂(ν : Measure Y))
      = ∫ p : X × Y, ψ p.2 ∂(π : Measure (X × Y)) := by
    rw [hν, integral_map measurable_snd.aemeasurable hψ.aestronglyMeasurable]
  rw [eφ, eψ, ← integral_add hφπ hψπ]
  exact integral_mono_ae (hφπ.add hψπ) hcπ
    (Filter.Eventually.of_forall fun p => hle p.1 p.2)

/-- A continuous real function on a nonempty compact space as a bounded continuous function. -/
private noncomputable def mkBCF
    {W : Type*} [TopologicalSpace W] [CompactSpace W] [Nonempty W]
    (f : W → ℝ) (hf : Continuous f) : W →ᵇ ℝ where
  toContinuousMap := ⟨f, hf⟩
  map_bounded' := by
    obtain ⟨z₁, -, hz₁⟩ :=
      isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.continuousOn
    obtain ⟨z₀, -, hz₀⟩ :=
      isCompact_univ.exists_isMinOn Set.univ_nonempty hf.continuousOn
    refine ⟨|f z₁| + |f z₀|, fun x y => ?_⟩
    rw [dist_eq_norm, Real.norm_eq_abs]
    have hx1 : f x ≤ f z₁ := isMaxOn_iff.mp hz₁ x (Set.mem_univ _)
    have hx0 : f z₀ ≤ f x := isMinOn_iff.mp hz₀ x (Set.mem_univ _)
    have hy1 : f y ≤ f z₁ := isMaxOn_iff.mp hz₁ y (Set.mem_univ _)
    have hy0 : f z₀ ≤ f y := isMinOn_iff.mp hz₀ y (Set.mem_univ _)
    have g1 : f z₁ ≤ |f z₁| := le_abs_self _
    have g2 : -(f z₀) ≤ |f z₀| := neg_le_abs _
    rw [abs_le]
    constructor <;> linarith

/-- ENNReal subtraction reverses strict inequality on compacta: helper for outer regularity. -/
private theorem ennreal_sub_lt_of_lt {a b r : ℝ≥0∞}
    (ha : a ≠ ∞) (hb : b ≠ ∞) (hr : r ≠ ∞) (hbr : b < r) (hra : r ≤ a) :
    a - r < a - b := by
  have hba : b ≤ a := hbr.le.trans hra
  have h1 : (a - r).toReal < (a - b).toReal := by
    rw [ENNReal.toReal_sub_of_le hra ha, ENNReal.toReal_sub_of_le hba ha]
    have hbr' : b.toReal < r.toReal := (ENNReal.toReal_lt_toReal hb hr).mpr hbr
    linarith
  have h2 : a - r ≠ ∞ := ne_top_of_le_ne_top ha tsub_le_self
  have h3 : a - b ≠ ∞ := ne_top_of_le_ne_top ha tsub_le_self
  exact (ENNReal.toReal_lt_toReal h2 h3).mp h1

/-- A finite Borel measure on a compact metric space is regular. -/
private instance regular_of_finite_compact_metric
    {W : Type*} [MetricSpace W] [CompactSpace W]
    [MeasurableSpace W] [BorelSpace W]
    {μ : Measure W} [IsFiniteMeasure μ] : μ.Regular := by
  have hfin : IsFiniteMeasureOnCompacts μ := ⟨by
    intro K hK
    exact lt_of_le_of_lt (measure_mono (Set.subset_univ _)) (measure_lt_top μ _)⟩
  have hinner_open : μ.InnerRegularWRT IsCompact IsOpen :=
    innerRegularWRT_isCompact_isOpen μ
  have hinner_meas : μ.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) MeasurableSet :=
    innerRegular_isCompact_isClosed_measurableSet_of_finite μ
  have houter : μ.OuterRegular := ⟨fun {A} hA r hr => by
    by_cases hrU : r ≤ μ Set.univ
    · have hAfin : μ A ≠ ∞ := measure_ne_top μ A
      have hUfin : μ Set.univ ≠ ∞ := measure_ne_top μ Set.univ
      have hrfin : r ≠ ∞ := ne_top_of_le_ne_top hUfin hrU
      have hcompl : μ Aᶜ = μ Set.univ - μ A := measure_compl hA hAfin
      have hr'lt : μ Set.univ - r < μ Aᶜ := by
        rw [hcompl]
        exact ennreal_sub_lt_of_lt hUfin hAfin hrfin hr hrU
      obtain ⟨K, hKA, ⟨hKcomp, hKclosed⟩, hr'K⟩ :=
        hinner_meas hA.compl (μ Set.univ - r) hr'lt
      have hKfin : μ K ≠ ∞ := measure_ne_top μ K
      have hKmeas : MeasurableSet K := hKclosed.measurableSet
      have hKU : μ K ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      refine ⟨Kᶜ, fun x hx => ?_, hKclosed.isOpen_compl, ?_⟩
      · simp only [Set.mem_compl_iff]
        exact fun hKx => hKA hKx hx
      · rw [measure_compl hKmeas hKfin]
        have h1 : (μ Set.univ - μ K).toReal < r.toReal := by
          rw [ENNReal.toReal_sub_of_le hKU hUfin]
          have hr'K' : (μ Set.univ - r).toReal < (μ K).toReal := by
            have hsub : μ Set.univ - r ≠ ∞ :=
              ne_top_of_le_ne_top hUfin tsub_le_self
            exact (ENNReal.toReal_lt_toReal hsub hKfin).mpr hr'K
          rw [ENNReal.toReal_sub_of_le hrU hUfin] at hr'K'
          linarith
        have h2 : μ Set.univ - μ K ≠ ∞ := ne_top_of_le_ne_top hUfin tsub_le_self
        exact (ENNReal.toReal_lt_toReal h2 hrfin).mp h1
    · exact ⟨Set.univ, Set.subset_univ _, isOpen_univ, lt_of_not_ge hrU⟩⟩
  exact Measure.Regular.mk (toIsFiniteMeasureOnCompacts := hfin)
    (toOuterRegular := houter) hinner_open

/-- Sum of a pair of bounded continuous functions as a function on the product. -/
private noncomputable def phiPlusPsi
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    (d : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) : (X × Y) →ᵇ ℝ :=
  mkBCF (fun z => d.1 z.1 + d.2 z.2)
    ((d.1.continuous.comp continuous_fst).add (d.2.continuous.comp continuous_snd))

private theorem phiPlusPsi_apply
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    (d : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) (z : X × Y) :
    phiPlusPsi d z = d.1 z.1 + d.2 z.2 := rfl

/-- The sum map as a linear map into bounded continuous functions on the product. -/
private noncomputable def PhiLM
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y] :
    ((X →ᵇ ℝ) × (Y →ᵇ ℝ)) →ₗ[ℝ] ((X × Y) →ᵇ ℝ) where
  toFun := phiPlusPsi
  map_add' d e := by
    apply BoundedContinuousFunction.ext
    intro z
    have h1 : (d + e).1 z.1 = d.1 z.1 + e.1 z.1 := rfl
    have h2 : (d + e).2 z.2 = d.2 z.2 + e.2 z.2 := rfl
    simp only [phiPlusPsi_apply, BoundedContinuousFunction.add_apply, h1, h2]
    ring
  map_smul' c d := by
    apply BoundedContinuousFunction.ext
    intro z
    have h1 : (c • d).1 z.1 = c • d.1 z.1 := rfl
    have h2 : (c • d).2 z.2 = c • d.2 z.2 := rfl
    simp only [phiPlusPsi_apply, BoundedContinuousFunction.smul_apply, h1, h2, smul_add,
      RingHom.id_apply]

/-- The dual objective as a linear map on pairs of bounded continuous functions. -/
private noncomputable def dualValLM
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [CompactSpace X] [CompactSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ((X →ᵇ ℝ) × (Y →ᵇ ℝ)) →ₗ[ℝ] ℝ where
  toFun d := (∫ x, d.1 x ∂μ) + ∫ y, d.2 y ∂ν
  map_add' d e := by
    have hφ1 : Integrable (fun x => d.1 x) μ :=
      integrable_continuous_compact _ d.1.continuous _
    have hφ2 : Integrable (fun x => e.1 x) μ :=
      integrable_continuous_compact _ e.1.continuous _
    have hψ1 : Integrable (fun y => d.2 y) ν :=
      integrable_continuous_compact _ d.2.continuous _
    have hψ2 : Integrable (fun y => e.2 y) ν :=
      integrable_continuous_compact _ e.2.continuous _
    have e1 : (fun x => (d + e).1 x) = (fun x => d.1 x + e.1 x) := rfl
    have e2 : (fun y => (d + e).2 y) = (fun y => d.2 y + e.2 y) := rfl
    change (∫ x, (d + e).1 x ∂μ) + ∫ y, (d + e).2 y ∂ν = _
    rw [e1, e2, integral_add hφ1 hφ2, integral_add hψ1 hψ2]
    ring
  map_smul' c d := by
    have e1 : (fun x => (c • d).1 x) = (fun x => c • d.1 x) := rfl
    have e2 : (fun y => (c • d).2 y) = (fun y => c • d.2 y) := rfl
    change (∫ x, (c • d).1 x ∂μ) + ∫ y, (c • d).2 y ∂ν = _
    simp only [e1, e2, integral_smul, smul_add, RingHom.id_apply]

/-- Dual values are bounded above (by any primal value). -/
private theorem dual_bddAbove
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) (hc : Continuous c) :
    BddAbove {r : ℝ | ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
      DualFeasible c φ ψ ∧
      r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)} := by
  refine ⟨∫ p, c p ∂((μ.prod ν) : Measure (X × Y)), ?_⟩
  rintro r ⟨φ, ψ, hfeas, rfl⟩
  obtain ⟨hφ, hψ, hle⟩ := hfeas
  exact dual_le_primal_of_isCoupling μ ν c hc φ ψ hφ hψ hle _ (isCoupling_prod μ ν)

/-- Primal values are bounded below (by the minimum of `c`). -/
private theorem primal_bddBelow
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) (hc : Continuous c) :
    BddBelow (primalValues μ ν c) := by
  obtain ⟨p₀, -, hp₀⟩ :=
    isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
  refine ⟨c p₀, ?_⟩
  rintro q ⟨π, hπ, rfl⟩
  have hmin : ∀ z, c p₀ ≤ c z := fun z => isMinOn_iff.mp hp₀ z (Set.mem_univ _)
  have h1 : Integrable c (π : Measure (X × Y)) :=
    integrable_continuous_compact _ hc _
  have h2 : Integrable (fun _ : X × Y => c p₀) (π : Measure (X × Y)) :=
    integrable_const _
  have hle := integral_mono_ae h2 h1 (Filter.Eventually.of_forall hmin)
  simpa using hle

/-- Key estimate: shifting a pair down by an upper bound on the violation stays
below the dual supremum. -/
private theorem key_le
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) (hc : Continuous c)
    (d : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) (m : ℝ) (hm : ∀ z, (PhiLM d) z - c z ≤ m) :
    (dualValLM (μ : Measure X) (ν : Measure Y) d) - m ≤ sSup {r : ℝ | ∃ φ : X → ℝ,
      ∃ ψ : Y → ℝ, DualFeasible c φ ψ ∧
      r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)} := by
  have hbdd := dual_bddAbove μ ν c hc
  have hmem : (dualValLM (μ : Measure X) (ν : Measure Y) d) - m ∈ {r : ℝ | ∃ φ : X → ℝ,
      ∃ ψ : Y → ℝ, DualFeasible c φ ψ ∧
      r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)} := by
    refine ⟨⇑(d.1 - BoundedContinuousFunction.const X m), ⇑d.2,
      ⟨(d.1 - BoundedContinuousFunction.const X m).continuous, d.2.continuous, ?_⟩, ?_⟩
    · intro x y
      have h := hm (x, y)
      rw [PhiLM_apply] at h
      have hc1 : (d.1 - BoundedContinuousFunction.const X m) x = d.1 x - m := rfl
      rw [hc1]
      linarith
    · have hint1 : Integrable (fun x => d.1 x) (μ : Measure X) :=
        integrable_continuous_compact _ d.1.continuous _
      have hcm : Integrable (fun _ : X => m) (μ : Measure X) := integrable_const _
      have eφ : (∫ x, (d.1 - BoundedContinuousFunction.const X m) x ∂(μ : Measure X))
          = (∫ x, d.1 x ∂(μ : Measure X)) - m := by
        have e : (fun x => (d.1 - BoundedContinuousFunction.const X m) x)
            = (fun x => d.1 x - m) := rfl
        rw [e, integral_sub hint1 hcm]
        congr 1
        simp
      have hval : (dualValLM (μ : Measure X) (ν : Measure Y) d)
          = (∫ x, d.1 x ∂(μ : Measure X)) + ∫ y, d.2 y ∂(ν : Measure Y) := rfl
      rw [hval, eφ]
      ring
  exact le_csSup hbdd hmem

/-- The affine map whose sublevel set (at `0`) is the separating set. -/
private noncomputable def sepMap
    {W : Type*} [TopologicalSpace W] (cb : W →ᵇ ℝ) (t : ℝ) :
    ((W →ᵇ ℝ) × ℝ) → (W →ᵇ ℝ) := fun p => p.1 - cb - (p.2 - t) • 1

/-- The separating open convex set: pairs strictly below the cost-shifted threshold. -/
private noncomputable def sepSet
    {W : Type*} [TopologicalSpace W] (cb : W →ᵇ ℝ) (t : ℝ) :
    Set ((W →ᵇ ℝ) × ℝ) := sepMap cb t ⁻¹' {w | ∀ z, w z < 0}

/-- The graph of the dual objective over the sum map, as a submodule. -/
private noncomputable def graphSub
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [CompactSpace X] [CompactSpace Y]
    [Nonempty X] [Nonempty Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Submodule ℝ (((X × Y) →ᵇ ℝ) × ℝ) :=
  LinearMap.range (LinearMap.prod PhiLM (dualValLM μ ν))

/-- Separation produces a positive linear functional dominating the dual objective. -/
private theorem exists_posFunctional
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) (hc : Continuous c)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Pim : ((X × Y) →ᵇ ℝ) →ₗ[ℝ] ℝ,
      (∀ w, (∀ z, 0 ≤ w z) → 0 ≤ Pim w) ∧
      (∀ d, Pim (PhiLM d) = dualValLM (μ : Measure X) (ν : Measure Y) d) ∧
      Pim (mkBCF c hc) ≤ sSup {r : ℝ | ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
        DualFeasible c φ ψ ∧
        r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)} + ε ∧
      Pim 1 = 1 := by
  set Dstar : ℝ := sSup {r : ℝ | ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
      DualFeasible c φ ψ ∧
      r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)}
  have hD : ∀ (d : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) (m : ℝ),
      (∀ z, (PhiLM d) z - c z ≤ m) →
      (dualValLM (μ : Measure X) (ν : Measure Y) d) - m ≤ Dstar :=
    fun d m hm => key_le μ ν c hc d m hm
  have hdisj := disjoint_graph_sepSet μ ν c hc Dstar ε hε hD
  have hUopen : IsOpen (sepSet (mkBCF c hc) (Dstar + ε)) := isOpen_sepSet _ _
  have hUconv : Convex ℝ (sepSet (mkBCF c hc) (Dstar + ε)) := convex_sepSet _ _
  have hMconv := Submodule.convex (graphSub (μ : Measure X) (ν : Measure Y))
  obtain ⟨F, γ, hUs, hMt⟩ := geometric_hahn_banach_open hUconv hUopen hMconv hdisj
  have hF0 : ∀ m : ((X × Y) →ᵇ ℝ) × ℝ,
      m ∈ (graphSub (μ : Measure X) (ν : Measure Y)) → F m = 0 := by
    intro m hm
    by_contra hne
    have hmem : ((γ - 1) / F m) • m ∈ (graphSub (μ : Measure X) (ν : Measure Y)) :=
      Submodule.smul_mem _ _ hm
    have hle := hMt _ hmem
    have hFm : F (((γ - 1) / F m) • m) = γ - 1 := by
      rw [F.map_smul, smul_eq_mul, div_mul_cancel₀ _ hne]
    linarith
  set Λ : ((X × Y) →ᵇ ℝ) →ₗ[ℝ] ℝ := F.toLinearMap.comp (LinearMap.inl ℝ _ _)
  have hΛeq : ∀ v, Λ v = F (v, 0) := fun v => rfl
  have hdecomp : ∀ p : ((X × Y) →ᵇ ℝ) × ℝ, F p = Λ p.1 + p.2 * F (0, 1) := by
    intro p
    have e : p = (p.1, 0) + p.2 • (0, 1) := by
      rw [Prod.ext_iff]
      constructor
      · change p.1 = p.1 + p.2 • (0 : (X × Y) →ᵇ ℝ)
        rw [smul_zero, add_zero]
      · change p.2 = (0 : ℝ) + p.2 • (1 : ℝ)
        rw [smul_eq_mul, mul_one, zero_add]
    conv_lhs => rw [e]
    rw [map_add, F.map_smul, smul_eq_mul, hΛeq]
  have h0mem : (0 : ((X × Y) →ᵇ ℝ) × ℝ)
      ∈ (graphSub (μ : Measure X) (ν : Measure Y)) := ⟨0, map_zero _⟩
  have hγ0 : γ ≤ 0 := by
    have hle := hMt _ h0mem
    rw [map_zero] at hle
    exact hle
  have hFne : F ≠ 0 := by
    intro hF0'
    obtain ⟨p₀, hp₀⟩ := nonempty_sepSet (mkBCF c hc) (Dstar + ε)
    have h1 := hUs p₀ hp₀
    have h2 := hMt _ h0mem
    rw [hF0'] at h1 h2
    simp at h1 h2
    linarith
  have hmemCB : ∀ t : ℝ, Dstar + ε < t →
      (mkBCF c hc, t) ∈ sepSet (mkBCF c hc) (Dstar + ε) := by
    intro t ht
    rw [sepSet_mem]
    intro z
    linarith
  have hα0 : F (0, 1) ≤ 0 := by
    by_contra hpos
    push Not at hpos
    set T : ℝ := max (Dstar + ε + 1) ((γ - F (mkBCF c hc, 0) + 1) / F (0, 1)) with hT
    have hT1 : Dstar + ε < T := by
      rw [hT]
      exact lt_max_iff.mpr (Or.inl (by linarith))
    have hlt := hUs _ (hmemCB T hT1)
    rw [hdecomp] at hlt
    have hlt' : Λ (mkBCF c hc) + T * F (0, 1) < γ := hlt
    have hT2 : ((γ - F (mkBCF c hc, 0) + 1) / F (0, 1)) ≤ T := by
      rw [hT]
      exact le_max_right _ _
    have hmul : ((γ - F (mkBCF c hc, 0) + 1) / F (0, 1)) * F (0, 1)
        = γ - F (mkBCF c hc, 0) + 1 := div_mul_cancel₀ _ (ne_of_gt hpos)
    have hge : γ - F (mkBCF c hc, 0) + 1 ≤ T * F (0, 1) := by
      rw [← hmul]
      exact mul_le_mul_of_nonneg_right hT2 (le_of_lt hpos)
    have hΛcb : Λ (mkBCF c hc) = F (mkBCF c hc, 0) := hΛeq _
    linarith
  have hpos : ∀ w : (X × Y) →ᵇ ℝ, (∀ z, 0 ≤ w z) → 0 ≤ F (w, 0) := by
    intro w hw
    by_contra hneg
    push Not at hneg
    have hmem : ∀ s : ℝ, 0 ≤ s →
        (mkBCF c hc - s • w, Dstar + ε + 1)
          ∈ sepSet (mkBCF c hc) (Dstar + ε) := by
      intro s hs
      rw [sepSet_mem]
      intro z
      have e1 : (mkBCF c hc - s • w) z = (mkBCF c hc) z - s * w z := by
        rw [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.smul_apply,
          smul_eq_mul]
      rw [e1]
      have hsw : 0 ≤ s * w z := mul_nonneg hs (hw z)
      have hD' : (Dstar + ε + 1) - (Dstar + ε) = 1 := by ring
      rw [hD']
      linarith
    set K : ℝ := |F (mkBCF c hc, 0) + (Dstar + ε + 1) * F (0, 1) - γ| + 1 with hK
    have hKpos : 0 < K := by
      rw [hK]
      linarith [abs_nonneg (F (mkBCF c hc, 0) + (Dstar + ε + 1) * F (0, 1) - γ)]
    set s : ℝ := K / (-F (w, 0)) with hs
    have hne : -F (w, 0) ≠ 0 := neg_ne_zero.mpr (ne_of_lt hneg)
    have hs0 : 0 ≤ s := by
      rw [hs]
      exact div_nonneg (le_of_lt hKpos) (le_of_lt (neg_pos.mpr hneg))
    have hlt := hUs _ (hmem s hs0)
    rw [hdecomp] at hlt
    have hlt' : Λ (mkBCF c hc - s • w) + (Dstar + ε + 1) * F (0, 1) < γ := hlt
    have hdec : Λ (mkBCF c hc - s • w)
        = Λ (mkBCF c hc) - s * Λ w := by
      simp only [map_sub, map_smulₛₗ, RingHom.id_apply, smul_eq_mul]
    rw [hdec] at hlt'
    have hsk : s * (-F (w, 0)) = K := by rw [hs]; exact div_mul_cancel₀ _ hne
    have hsk2 : -(s * F (w, 0)) = K := by rw [← hsk]; ring
    have hΛw : Λ w = F (w, 0) := hΛeq _
    have hsk3 : Λ (mkBCF c hc) - s * Λ w = Λ (mkBCF c hc) + K := by
      rw [hΛw, ← hsk2]; ring
    rw [hsk3, hK] at hlt'
    have habs := neg_le_abs (F (mkBCF c hc, 0) + (Dstar + ε + 1) * F (0, 1) - γ)
    have hΛcb : Λ (mkBCF c hc) = F (mkBCF c hc, 0) := hΛeq _
    linarith
  have hgraph : ∀ d : (X →ᵇ ℝ) × (Y →ᵇ ℝ),
      Λ (PhiLM d) + (dualValLM (μ : Measure X) (ν : Measure Y) d) * F (0, 1) = 0 := by
    intro d
    have hm : (PhiLM d, dualValLM (μ : Measure X) (ν : Measure Y) d)
        ∈ (graphSub (μ : Measure X) (ν : Measure Y)) := ⟨d, rfl⟩
    have h0 := hF0 _ hm
    rw [hdecomp] at h0
    have h0' : Λ (PhiLM d)
        + (dualValLM (μ : Measure X) (ν : Measure Y) d) * F (0, 1) = 0 := h0
    exact h0'
  have hαne : F (0, 1) ≠ 0 := by
    intro hα0
    have hΛlt : ∀ v : (X × Y) →ᵇ ℝ, F (v, 0) < γ := by
      intro v
      obtain ⟨z₀, hz₀⟩ := exists_max_attain (v - mkBCF c hc)
      have hmem : (v, Dstar + ε + (v - mkBCF c hc) z₀ + 1)
          ∈ sepSet (mkBCF c hc) (Dstar + ε) := by
        rw [sepSet_mem]
        intro z
        have hle : v z - (mkBCF c hc) z ≤ (v - mkBCF c hc) z₀ := by
          have h := hz₀ z
          have e : ∀ w : X × Y, (v - mkBCF c hc) w = v w - (mkBCF c hc) w :=
            fun w => rfl
          rwa [e z] at h
        linarith
      have h := hUs _ hmem
      rw [hdecomp] at h
      have h' : Λ v + (Dstar + ε + (v - mkBCF c hc) z₀ + 1) * F (0, 1) < γ := h
      rw [hα0, mul_zero, add_zero] at h'
      rw [hΛeq] at h'
      exact h'
    have hΛ0 : ∀ v : (X × Y) →ᵇ ℝ, F (v, 0) = 0 := by
      intro v
      by_contra hnev
      have hlt := hΛlt (((γ + 1) / F (v, 0)) • v)
      have hsc : F ((((γ + 1) / F (v, 0)) • v), 0) = γ + 1 := by
        have e1 : F ((((γ + 1) / F (v, 0)) • v), 0)
            = Λ ((((γ + 1) / F (v, 0)) • v)) := (hΛeq _).symm
        rw [e1, map_smulₛₗ, RingHom.id_apply, smul_eq_mul, hΛeq]
        exact div_mul_cancel₀ _ hnev
      linarith
    have hFall : F = 0 := by
      apply ContinuousLinearMap.ext
      intro p
      rw [hdecomp]
      have h1 : Λ p.1 = 0 := by rw [hΛeq]; exact hΛ0 p.1
      rw [h1, hα0, mul_zero, add_zero]
      rfl
    exact hFne hFall
  have hαneg : F (0, 1) < 0 := lt_of_le_of_ne hα0 hαne
  have hsmul : ∀ v : (X × Y) →ᵇ ℝ,
      (((-F (0, 1))⁻¹ • Λ) v) = (-F (0, 1))⁻¹ * Λ v := by
    intro v
    rw [LinearMap.smul_apply, smul_eq_mul]
  have hPimPhi : ∀ d : (X →ᵇ ℝ) × (Y →ᵇ ℝ),
      (((-F (0, 1))⁻¹ • Λ) (PhiLM d))
        = dualValLM (μ : Measure X) (ν : Measure Y) d := by
    intro d
    rw [hsmul]
    have hgr := hgraph d
    have hF0' : Λ (PhiLM d)
        = -((dualValLM (μ : Measure X) (ν : Measure Y) d) * F (0, 1)) := by
      linarith
    rw [hF0']
    have hαne' : -F (0, 1) ≠ 0 := neg_ne_zero.mpr hαne
    have hinv : (-F (0, 1))⁻¹ * (-F (0, 1)) = 1 := inv_mul_cancel₀ hαne'
    linear_combination (dualValLM (μ : Measure X) (ν : Measure Y) d) * hinv
  have hposPim : ∀ w : (X × Y) →ᵇ ℝ, (∀ z, 0 ≤ w z)
      → 0 ≤ (((-F (0, 1))⁻¹ • Λ) w) := by
    intro w hw
    rw [hsmul]
    have hΛw : 0 ≤ Λ w := by rw [hΛeq]; exact hpos w hw
    have hpos2 : (0:ℝ) ≤ (-F (0, 1))⁻¹ :=
      le_of_lt (inv_pos.mpr (neg_pos.mpr hαneg))
    exact mul_nonneg hpos2 hΛw
  have hlePim : (((-F (0, 1))⁻¹ • Λ) (mkBCF c hc)) ≤ Dstar + ε := by
    have hpos2 : (0:ℝ) < (-F (0, 1))⁻¹ := inv_pos.mpr (neg_pos.mpr hαneg)
    have hlt : ∀ t : ℝ, Dstar + ε < t
        → Λ (mkBCF c hc) + t * F (0, 1) < γ := by
      intro t ht
      have h := hUs _ (hmemCB t ht)
      rw [hdecomp] at h
      have h' : Λ (mkBCF c hc) + t * F (0, 1) < γ := h
      exact h'
    have hPimlt : ∀ t : ℝ, Dstar + ε < t →
        (((-F (0, 1))⁻¹ • Λ) (mkBCF c hc)) < t + (-F (0, 1))⁻¹ * γ := by
      intro t ht
      rw [hsmul]
      have h := hlt t ht
      have hmul := mul_lt_mul_of_pos_left h hpos2
      have hαne' : -F (0, 1) ≠ 0 := neg_ne_zero.mpr hαne
      have hinv : (-F (0, 1))⁻¹ * (-F (0, 1)) = 1 := inv_mul_cancel₀ hαne'
      have h2 : (-F (0, 1))⁻¹ * (t * F (0, 1)) = -t := by
        linear_combination (-t) * hinv
      have heq : (-F (0, 1))⁻¹ * (Λ (mkBCF c hc) + t * F (0, 1))
          = (-F (0, 1))⁻¹ * Λ (mkBCF c hc) - t := by
        calc (-F (0, 1))⁻¹ * (Λ (mkBCF c hc) + t * F (0, 1))
            = (-F (0, 1))⁻¹ * Λ (mkBCF c hc)
              + (-F (0, 1))⁻¹ * (t * F (0, 1)) := by ring
          _ = (-F (0, 1))⁻¹ * Λ (mkBCF c hc) + (-t) := by rw [h2]
          _ = (-F (0, 1))⁻¹ * Λ (mkBCF c hc) - t := by ring
      linarith
    have hle1 : (((-F (0, 1))⁻¹ • Λ) (mkBCF c hc))
        ≤ Dstar + ε + (-F (0, 1))⁻¹ * γ := by
      apply le_of_forall_gt_imp_ge_of_dense
      intro b hb
      have ht : Dstar + ε
          < Dstar + ε + (b - (Dstar + ε + (-F (0, 1))⁻¹ * γ)) / 2 := by
        have hδ : (0:ℝ) < b - (Dstar + ε + (-F (0, 1))⁻¹ * γ) := by linarith
        linarith
      have h := hPimlt _ ht
      linarith
    have hcorr : (-F (0, 1))⁻¹ * γ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hpos2) hγ0
    linarith
  have h1Pim : (((-F (0, 1))⁻¹ • Λ) 1) = 1 := by
    have h1 : (1 : (X × Y) →ᵇ ℝ) = PhiLM (1, 0) := by
      apply BoundedContinuousFunction.ext
      intro z
      rw [PhiLM_apply]
      have e1 : ((1, 0) : (X →ᵇ ℝ) × (Y →ᵇ ℝ)).1 z.1 = 1 := rfl
      have e2 : ((1, 0) : (X →ᵇ ℝ) × (Y →ᵇ ℝ)).2 z.2 = 0 := rfl
      have e3 : (1 : (X × Y) →ᵇ ℝ) z = 1 := rfl
      rw [e1, e2, e3]
      ring
    rw [h1]
    rw [hPimPhi]
    have hL1 : (dualValLM (μ : Measure X) (ν : Measure Y) (1, 0)) = 1 := by
      have e : (dualValLM (μ : Measure X) (ν : Measure Y) (1, 0))
          = (∫ x, ((1, 0) : (X →ᵇ ℝ) × (Y →ᵇ ℝ)).1 x ∂(μ : Measure X))
            + ∫ y, ((1, 0) : (X →ᵇ ℝ) × (Y →ᵇ ℝ)).2 y ∂(ν : Measure Y) := rfl
      rw [e]
      have e1 : (fun x => ((1, 0) : (X →ᵇ ℝ) × (Y →ᵇ ℝ)).1 x)
          = (fun _ => (1:ℝ)) := rfl
      have e2 : (fun y => ((1, 0) : (X →ᵇ ℝ) × (Y →ᵇ ℝ)).2 y)
          = (fun _ => (0:ℝ)) := rfl
      rw [e1, e2]
      have i1 : (∫ _, (1:ℝ) ∂(μ : Measure X)) = 1 := by simp
      have i0 : (∫ _, (0:ℝ) ∂(ν : Measure Y)) = 0 := by simp
      rw [i1, i0, add_zero]
    exact hL1
  exact ⟨(-F (0, 1))⁻¹ • Λ, hposPim, hPimPhi, hlePim, h1Pim⟩

/-- The first marginal of a finite measure is finite. -/
private instance isFiniteMeasure_map_fst
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure (X × Y)} [IsFiniteMeasure μ] :
    IsFiniteMeasure (μ.map Prod.fst) :=
  Measure.isFiniteMeasure_map μ Prod.fst

/-- The second marginal of a finite measure is finite. -/
private instance isFiniteMeasure_map_snd
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure (X × Y)} [IsFiniteMeasure μ] :
    IsFiniteMeasure (μ.map Prod.snd) :=
  Measure.isFiniteMeasure_map μ Prod.snd

/-- Pullback of a compactly supported function along `Prod.fst`. -/
private noncomputable def fstCC
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y]
    (f : C_c(X, ℝ)) : C_c(X × Y, ℝ) :=
  CompactlySupportedContinuousMap.continuousMapEquiv
    ⟨fun z => f z.1, f.toBoundedContinuousFunction.continuous.comp continuous_fst⟩

/-- Pullback of a compactly supported function along `Prod.snd`. -/
private noncomputable def sndCC
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y]
    (g : C_c(Y, ℝ)) : C_c(X × Y, ℝ) :=
  CompactlySupportedContinuousMap.continuousMapEquiv
    ⟨fun z => g z.2, g.toBoundedContinuousFunction.continuous.comp continuous_snd⟩

/--
Strong duality on nonempty compact metric Borel spaces: for continuous `c : X × Y → ℝ`, `inf_π ∫ c
dπ = sup_{φ,ψ} ∫ φ dμ + ∫ ψ dν` over couplings `π` and continuous potentials `φ, ψ` with `φ x + ψ y
≤ c (x,y)`.
Source: L. V. Kantorovich, On the Translocation of Masses (1942); English transl. J. Math. Sci. 133
(2006), 1381-1382, DOI 10.1007/S10958-006-0049-2; modern ref C. Villani, Topics in Optimal
Transportation (2003).

Proves `Wanted` entry `kantorovich_duality_compact`.
-/
theorem kantorovich_duality_compact
    {X Y : Type*}
    [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    [Nonempty X] [Nonempty Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) (hc : Continuous c) :
    sInf (primalValues μ ν c) =
    sSup {r : ℝ | ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
      DualFeasible c φ ψ ∧
      r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)} := by
  have hP : (primalValues μ ν c).Nonempty := primalValues_nonempty μ ν c
  have hD : {r : ℝ | ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
      DualFeasible c φ ψ ∧
      r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)}.Nonempty :=
    dualValues_nonempty μ ν c hc
  apply le_antisymm
  · have hε : ∀ ε : ℝ, 0 < ε → sInf (primalValues μ ν c) ≤ sSup {r : ℝ |
        ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
        DualFeasible c φ ψ ∧
        r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)} + ε := by
      intro ε hε
      obtain ⟨Pim, hpos, hPhi, hcost, hone⟩ := exists_posFunctional μ ν c hc ε hε
      obtain ⟨π, hcoup, hle⟩ :=
        coupling_of_posFunctional μ ν c hc _ ε Pim hpos hPhi hcost hone
      have hmem : (∫ p, c p ∂(π : Measure (X × Y))) ∈ primalValues μ ν c :=
        ⟨π, hcoup, rfl⟩
      have hbdd := primal_bddBelow μ ν c hc
      exact le_trans (csInf_le hbdd hmem) hle
    apply le_of_forall_gt_imp_ge_of_dense
    intro b hb
    have h := hε (b - sSup {r : ℝ | ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
      DualFeasible c φ ψ ∧
      r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)}) (by linarith)
    linarith
  · apply csSup_le hD
    rintro r ⟨φ, ψ, hfeas, rfl⟩
    apply le_csInf hP
    rintro q ⟨π, hπ, rfl⟩
    obtain ⟨hφ, hψ, hle⟩ := hfeas
    exact dual_le_primal_of_isCoupling μ ν c hc φ ψ hφ hψ hle π hπ

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted
end
