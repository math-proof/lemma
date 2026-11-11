/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/CramerTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Sequences
import Theorem.v1.Atlas.Probability.code.CramerTheorem
import Theorem.v1.Atlas.Probability.code.CramerRateIDCore
import Theorem.v1.Atlas.Probability.code.LDPContraction
import Lemma.Random.SatisfiesLDP
import Lemma.Random.IsProbabilityMeasure.of.Gt_0
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.DominatedConvergence
open ENNReal Filter InformationTheory MeasureTheory ProbabilityMeasure ProbabilityTheory Random
open scoped Topology ENNReal InnerProductSpace

/-!
# Barycenter continuity under uniform exponential moments

Packages sequential barycenter continuity from `CramerTheorem` on the `UniformExpMoment`
subtype. On a sequential (e.g. metrizable) subtype, `SeqContinuous` upgrades to `Continuous`.

## Residual for full contraction on raw `ProbabilityMeasure`

* Empirical measures are not a.s. in a fixed `UniformExpMoment` ball; need exponential
  tightness into moment balls, or R→∞ truncation via `continuous_integral_radialClamp`.
* Giry vs weak topology: use `satisfiesLDP_map_of_continuous_of_measurable` with a separate
  Giry-measurability proof; do not rely on `Continuous.measurable` on `ProbabilityMeasure`.
-/

/-- Probability measures with a uniform `exp((2c)‖·‖)` moment bound and integrable identity. -/
def UniformExpMoment (d : ℕ) (c M : ℝ) : Type _ :=
  { ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) //
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.toMeasure ∧
      Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp ((2 * c) * ‖x‖)) ν.toMeasure ∧
        (∫ x, Real.exp ((2 * c) * ‖x‖) ∂ν.toMeasure) ≤ M }

namespace UniformExpMoment

@[simp] theorem val_mk {d : ℕ} {c M : ℝ}
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (h : Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.toMeasure ∧
      Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp ((2 * c) * ‖x‖)) ν.toMeasure ∧
        (∫ x, Real.exp ((2 * c) * ‖x‖) ∂ν.toMeasure) ≤ M) :
    (⟨ν, h⟩ : UniformExpMoment d c M).val = ν := rfl

instance {d : ℕ} {c M : ℝ} : TopologicalSpace (UniformExpMoment d c M) :=
  inferInstanceAs (TopologicalSpace
    { ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) //
      Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.toMeasure ∧
        Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp ((2 * c) * ‖x‖)) ν.toMeasure ∧
          (∫ x, Real.exp ((2 * c) * ‖x‖) ∂ν.toMeasure) ≤ M })

theorem integrable_id {d : ℕ} {c M : ℝ} (ν : UniformExpMoment d c M) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.val.toMeasure :=
  ν.property.1

theorem integrable_exp {d : ℕ} {c M : ℝ} (ν : UniformExpMoment d c M) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp ((2 * c) * ‖x‖))
      ν.val.toMeasure :=
  ν.property.2.1

theorem exp_moment_le {d : ℕ} {c M : ℝ} (ν : UniformExpMoment d c M) :
    (∫ x, Real.exp ((2 * c) * ‖x‖) ∂ν.val.toMeasure) ≤ M :=
  ν.property.2.2

/-- Barycenter restricted to the uniform-exp-moment subclass. -/
noncomputable def barycenterMap {d : ℕ} {c M : ℝ} (ν : UniformExpMoment d c M) :
    EuclideanSpace ℝ (Fin d) :=
  barycenter ν.val

/-- Sequential continuity of `barycenterMap` under a positive moment rate and nonnegative bound. -/
theorem seqContinuous_barycenterMap {d : ℕ} {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M) :
    SeqContinuous (barycenterMap (d := d) (c := c) (M := M)) := by
  intro νseq νlim hlim
  have hlim' : Tendsto (fun n => (νseq n).val) atTop (𝓝 νlim.val) :=
    (continuous_subtype_val.tendsto νlim).comp hlim
  -- Unfold `barycenterMap` so the CT lemma applies verbatim.
  change Tendsto (fun n => barycenter (νseq n).val) atTop (𝓝 (barycenter νlim.val))
  exact tendsto_barycenter_of_tendsto_of_uniform_exp_moment hc hM hlim'
    (fun n => (νseq n).integrable_id) νlim.integrable_id
    (fun n => (νseq n).integrable_exp) νlim.integrable_exp
    (fun n => (νseq n).exp_moment_le) νlim.exp_moment_le

/-- Continuity of barycenter on `UniformExpMoment` when the subtype is sequential. -/
theorem continuous_barycenterMap {d : ℕ} {c M : ℝ}
    [SequentialSpace (UniformExpMoment d c M)]
    (hc : 0 < c) (hM : 0 ≤ M) :
    Continuous (barycenterMap (d := d) (c := c) (M := M)) :=
  (seqContinuous_barycenterMap hc hM).continuous

/-- Borel measurability of `barycenterMap` on a sequential `UniformExpMoment` ball. -/
theorem measurable_barycenterMap {d : ℕ} {c M : ℝ}
    [SequentialSpace (UniformExpMoment d c M)]
    [MeasurableSpace (UniformExpMoment d c M)] [BorelSpace (UniformExpMoment d c M)]
    (hc : 0 < c) (hM : 0 ≤ M) :
    Measurable (barycenterMap (d := d) (c := c) (M := M)) :=
  (continuous_barycenterMap hc hM).measurable

/-- Sequential contraction for `barycenterMap` on a sequential Borel subtype. -/
theorem satisfiesLDP_map_barycenterMap_of_seq {d : ℕ} {c M : ℝ}
    [SequentialSpace (UniformExpMoment d c M)]
    [MeasurableSpace (UniformExpMoment d c M)] [BorelSpace (UniformExpMoment d c M)]
    {μ : ℕ → Measure (UniformExpMoment d c M)} {I : UniformExpMoment d c M → ENNReal}
    (hLDP : SatisfiesLDP μ I) (hc : 0 < c) (hM : 0 ≤ M)
    (hJ : LowerSemicontinuous (contractedRate I barycenterMap)) :
    SatisfiesLDP (fun n => (μ n).map barycenterMap) (contractedRate I barycenterMap) :=
  satisfiesLDP_map_of_seqContinuous hLDP barycenterMap
    (seqContinuous_barycenterMap hc hM) hJ

end UniformExpMoment

/-- Truncated means remain the continuous stand-in on raw `ProbabilityMeasure`. -/
theorem continuous_integral_radialClamp_reexport {d : ℕ} {R : ℝ} (hR : 0 < R) :
    Continuous fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
      ∫ x, radialClamp R x ∂ν.toMeasure :=
  continuous_integral_radialClamp hR


/-! ### Giry-measurable truncated means and Sanov contraction -/

/-- Giry-measurable real integrals of bounded continuous test functions against
`ProbabilityMeasure` (positive/negative parts via `measurable_lintegral`). -/
theorem measurable_integral_boundedContinuous
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α]
    (f : BoundedContinuousFunction α ℝ) :
    Measurable fun ν : ProbabilityMeasure α => ∫ x, f x ∂(ν : Measure α) := by
  have heq :
      (fun ν : ProbabilityMeasure α => ∫ x, f x ∂(ν : Measure α)) =
        fun ν : ProbabilityMeasure α =>
          (∫⁻ x, ENNReal.ofReal (f x) ∂(ν : Measure α)).toReal -
            (∫⁻ x, ENNReal.ofReal (-f x) ∂(ν : Measure α)).toReal := by
    funext ν
    have hint : Integrable (⇑f) (ν : Measure α) := by
      refine ⟨f.continuous.aestronglyMeasurable, ?_⟩
      refine HasFiniteIntegral.of_bounded (C := ‖f‖) (ae_of_all _ fun x => f.norm_coe_le_norm x)
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint
  rw [heq]
  refine Measurable.sub ?_ ?_
  · exact measurable_toReal.comp
      ((Measure.measurable_lintegral
          (measurable_ofReal.comp f.continuous.measurable)).comp measurable_subtype_coe)
  · exact measurable_toReal.comp
      ((Measure.measurable_lintegral
          (measurable_ofReal.comp f.continuous.neg.measurable)).comp measurable_subtype_coe)

/-- Coordinate of the truncated barycenter is Giry-measurable. -/
theorem measurable_eval_integral_radialClamp {d : ℕ} {R : ℝ} (hR : 0 < R) (i : Fin d) :
    Measurable fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
      (∫ x, radialClamp R x ∂ν.toMeasure) i := by
  have hι : Continuous (radialClamp (E := EuclideanSpace ℝ (Fin d)) R) := continuous_radialClamp hR
  let fCont : C(EuclideanSpace ℝ (Fin d), ℝ) :=
    ⟨fun x => radialClamp R x i, (PiLp.continuous_apply 2 _ i).comp hι⟩
  have hbound : ∀ x y : EuclideanSpace ℝ (Fin d),
      dist (fCont x) (fCont y) ≤ 2 * R := by
    intro x y
    have hx : ‖radialClamp R x‖ ≤ R := norm_radialClamp_le hR.le x
    have hy : ‖radialClamp R y‖ ≤ R := norm_radialClamp_le hR.le y
    have hx' : |radialClamp R x i| ≤ ‖radialClamp R x‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (radialClamp R x) i
    have hy' : |radialClamp R y i| ≤ ‖radialClamp R y‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (radialClamp R y) i
    calc dist (fCont x) (fCont y)
        = ‖fCont x - fCont y‖ := rfl
      _ ≤ ‖fCont x‖ + ‖fCont y‖ := norm_sub_le _ _
      _ ≤ R + R := by
          simp only [fCont, ContinuousMap.coe_mk, Real.norm_eq_abs]
          exact add_le_add (hx'.trans hx) (hy'.trans hy)
      _ = 2 * R := by ring
  let f : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ :=
    BoundedContinuousFunction.mkOfBound fCont (2 * R) hbound
  have hbcf := measurable_integral_boundedContinuous f
  have heq :
      (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) => ∫ x, f x ∂(ν : Measure _)) =
        fun ν => (∫ x, radialClamp R x ∂ν.toMeasure) i := by
    funext ν
    have hint' : Integrable (fun x => radialClamp R x) ν.toMeasure :=
      Integrable.mono' (integrable_const (μ := ν.toMeasure) R) hι.aestronglyMeasurable
        (Eventually.of_forall fun x => by simpa using norm_radialClamp_le hR.le x)
    change (∫ x, radialClamp R x i ∂ν.toMeasure) = (∫ x, radialClamp R x ∂ν.toMeasure) i
    exact (eval_integral_piLp (integrable_piLp_iff.mp hint') i).symm
  exact heq ▸ hbcf

/-- Truncated barycenter is Giry-measurable as an `EuclideanSpace`-valued map. -/
theorem measurable_integral_radialClamp {d : ℕ} {R : ℝ} (hR : 0 < R) :
    Measurable fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
      ∫ x, radialClamp R x ∂ν.toMeasure := by
  have hpi : Measurable fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
      (fun i : Fin d => (∫ x, radialClamp R x ∂ν.toMeasure) i) :=
    Measurable.of_eval fun i => measurable_eval_integral_radialClamp hR i
  have h :=
    (MeasurableEquiv.toLp (2 : ℝ≥0∞) (Fin d → ℝ)).measurable.comp hpi
  convert h using 1
  funext ν
  exact (WithLp.toLp_ofLp (p := (2 : ℝ≥0∞)) (∫ x, radialClamp R x ∂ν.toMeasure)).symm

/-- Sanov LDP pushed through the continuous+Giry-measurable truncated mean.
Takes an already-established Sanov LDP hyp so the empirical encoding stays flexible. -/
theorem satisfiesLDP_map_integral_radialClamp {d : ℕ} {R : ℝ} (hR : 0 < R)
    {μ : ℕ → Measure (ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))}
    {I : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) → ENNReal}
    (hLDP : SatisfiesLDP μ I)
    (hJ : LowerSemicontinuous
      (contractedRate I
        (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
          ∫ x, radialClamp R x ∂ν.toMeasure))) :
    SatisfiesLDP
      (fun n => (μ n).map
        (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
          ∫ x, radialClamp R x ∂ν.toMeasure))
      (contractedRate I
        (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
          ∫ x, radialClamp R x ∂ν.toMeasure)) :=
  satisfiesLDP_map_of_continuous_of_measurable hLDP
    (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
      ∫ x, radialClamp R x ∂ν.toMeasure)
    (continuous_integral_radialClamp hR)
    (measurable_integral_radialClamp hR) hJ

/-- The reference law itself sits in every positive-rate `UniformExpMoment` ball
whose moment bound dominates `∫ exp((2c)‖·‖) dμ₀`. -/
noncomputable def HasFiniteMGF.toUniformExpMoment {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀) {c M : ℝ} (_hc : 0 < c)
    (hM : (∫ x, Real.exp ((2 * c) * ‖x‖) ∂μ₀) ≤ M) :
    UniformExpMoment d c M :=
  ⟨μ₀.toProbabilityMeasure, ⟨hMGF.integrable_id, hMGF.integrable_exp_mul_norm (2 * c), by
    simpa using hM⟩⟩

/-! ### Giry measurability of barycenter on `FiniteFirstMoment` via clamp limits -/

/-- On measures with finite first moment, the barycenter is the pointwise limit of Giry-measurable
truncated means, hence Giry-measurable on the subtype. -/
theorem FiniteFirstMoment.measurable_barycenterMap {d : ℕ} :
    Measurable (FiniteFirstMoment.barycenterMap (d := d)) := by
  have hclamp : ∀ n : ℕ,
      Measurable fun ν : FiniteFirstMoment d =>
        ∫ x, radialClamp ((n : ℝ) + 1) x ∂ν.val.toMeasure := by
    intro n
    exact (measurable_integral_radialClamp (Nat.cast_add_one_pos n)).comp measurable_subtype_coe
  refine measurable_of_tendsto_metrizable hclamp ?_
  refine tendsto_pi_nhds.mpr fun ν => ?_
  simpa [FiniteFirstMoment.barycenterMap] using
    tendsto_integral_radialClamp_barycenter ν.val ν.integrable

/-- Identity is integrable on every `FiniteFirstMoment` fiber (records the subtype `hid`). -/
theorem FiniteFirstMoment.integrable_id_of_barycenter_eq {d : ℕ}
    (y : EuclideanSpace ℝ (Fin d))
    (ν : FiniteFirstMoment d)
    (_h : FiniteFirstMoment.barycenterMap ν = y) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.val.toMeasure :=
  ν.integrable

/-! ### Truncation residual of barycenters under uniform exp moments -/

/-- Under a uniform `exp((2c)‖·‖)` moment bound, barycenter and truncated mean are
uniformly close for large R (deterministic, measure-level). -/
theorem dist_barycenter_integral_radialClamp_le_of_expMoment {d : ℕ}
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    {c M R : ℝ} (hc : 0 < c) (hR : 0 < R) (hM : 0 ≤ M)
    (hint : Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.toMeasure)
    (hexp : Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp ((2 * c) * ‖x‖))
      ν.toMeasure)
    (hbound : (∫ x, Real.exp ((2 * c) * ‖x‖) ∂ν.toMeasure) ≤ M) :
    dist (barycenter ν) (∫ x, radialClamp R x ∂ν.toMeasure) ≤
      (2 / c) * Real.exp (-c * R) * M := by
  have h := norm_barycenter_sub_integral_radialClamp_le ν hc hR hint hexp
  refine (dist_eq_norm _ _).trans_le (h.trans ?_)
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

/-- Choose R so every measure in a UniformExpMoment ball has clamp residual ≤ ε. -/
theorem exists_radius_uniform_clamp_approx {d : ℕ} {c M ε : ℝ}
    (hc : 0 < c) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧
      ∀ ν : UniformExpMoment d c M,
        dist (UniformExpMoment.barycenterMap ν)
          (∫ x, radialClamp R x ∂ν.val.toMeasure) ≤ ε := by
  obtain ⟨R, hR, htail⟩ := exists_radius_exp_tail_le hc hM hε
  refine ⟨R, hR, fun ν => ?_⟩
  have h := dist_barycenter_integral_radialClamp_le_of_expMoment ν.val
    hc hR hM ν.integrable_id ν.integrable_exp ν.exp_moment_le
  simpa [UniformExpMoment.barycenterMap] using h.trans htail


/-! ### R→∞ truncation scaffolding toward empirical-mean LDP -/

/-- For every `ε > 0`, eventually in `R` (atTop) the clamp residual is `≤ ε`
uniformly on the `UniformExpMoment` ball. -/
theorem eventually_uniform_clamp_approx {d : ℕ} {c M ε : ℝ}
    (hc : 0 < c) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop,
      0 < R ∧
        ∀ ν : UniformExpMoment d c M,
          dist (UniformExpMoment.barycenterMap ν)
            (∫ x, radialClamp R x ∂ν.val.toMeasure) ≤ ε := by
  obtain ⟨R0, hR0, htail⟩ := exists_radius_exp_tail_le hc hM hε
  refine Filter.eventually_atTop.mpr ⟨R0, fun R hRge => ?_⟩
  have hR : 0 < R := lt_of_lt_of_le hR0 hRge
  refine ⟨hR, fun ν => ?_⟩
  have h := dist_barycenter_integral_radialClamp_le_of_expMoment ν.val
    hc hR hM ν.integrable_id ν.integrable_exp ν.exp_moment_le
  have hexp_le : Real.exp (-c * R) ≤ Real.exp (-c * R0) := by
    apply Real.exp_le_exp.mpr
    -- (-c) * R ≤ (-c) * R0 because -c ≤ 0 and R0 ≤ R
    exact mul_le_mul_of_nonpos_left hRge (neg_nonpos.mpr hc.le)
  have hbound :
      (2 / c) * Real.exp (-c * R) * M ≤ (2 / c) * Real.exp (-c * R0) * M := by
    refine mul_le_mul_of_nonneg_right ?_ hM
    exact mul_le_mul_of_nonneg_left hexp_le (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc.le)
  exact (h.trans hbound).trans htail

/-- Sequential continuity package: on any sequential `UniformExpMoment` ball,
Sanov contracts through the true barycenter (no raw Continuous on all
`ProbabilityMeasure`). Exponential tightness into some ball remains residual. -/
theorem satisfiesLDP_map_barycenterMap_of_seq_of_HasFiniteMGF {d : ℕ} {c M : ℝ}
    [SequentialSpace (UniformExpMoment d c M)]
    [MeasurableSpace (UniformExpMoment d c M)] [BorelSpace (UniformExpMoment d c M)]
    {μ : ℕ → Measure (UniformExpMoment d c M)}
    {I : UniformExpMoment d c M → ENNReal}
    (hLDP : SatisfiesLDP μ I)
    (hc : 0 < c) (hM : 0 ≤ M)
    (hJ : LowerSemicontinuous (contractedRate I UniformExpMoment.barycenterMap)) :
    SatisfiesLDP (fun n => (μ n).map UniformExpMoment.barycenterMap)
      (contractedRate I UniformExpMoment.barycenterMap) :=
  UniformExpMoment.satisfiesLDP_map_barycenterMap_of_seq hLDP hc hM hJ


/-! ### Sanov → empirical-mean LDP under Cont/Meas barycenter

Packages Random's contraction step on Theorem side so the public wrapper only needs
`hLDP`. Continuous/Measurable barycenter on raw `ProbabilityMeasure` is still false
in general; discharge it via UniformExpMoment exp-tightness or R→∞ clamp truncation
(`satisfiesLDP_map_integral_radialClamp` + exp-equivalence). Fiber `hid` is already
internalized under `HasFiniteMGF` in `CramerRateID` /
`integrable_id_of_klDiv_ne_top_of_HasFiniteMGF`.
-/

/-- Polish Sanov written with `empiricalProbabilityMeasure` (definitionally the Sanov law). -/
theorem satisfiesLDP_sanov_empiricalProbabilityMeasure
    {d : ℕ} {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀] :
    SatisfiesLDP
      (fun n =>
        Measure.map
          (fun ω : Fin n → EuclideanSpace ℝ (Fin d) =>
            if hn : 0 < n then empiricalProbabilityMeasure hn ω
            else μ₀.toProbabilityMeasure)
          (Measure.pi fun _ : Fin n => μ₀))
      (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
        klDiv (ν : Measure _) μ₀) := by
  convert SatisfiesLDP (μ := μ₀)
  · refine dite_congr rfl ?_ ?_
    · intro hn; rfl
    · intro h; rfl

/-- Tail agreement of measure sequences preserves the LDP. -/
theorem satisfiesLDP_congr_eventually
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ ν : ℕ → Measure X} {I : X → ENNReal}
    (h : SatisfiesLDP μ I)
    (heq : ∀ᶠ n in atTop, μ n = ν n) :
    SatisfiesLDP ν I := by
  refine ⟨h.isRateFunction, ?_, ?_⟩
  · intro U hU
    have hlb := h.lower_bound U hU
    have hfun :
        (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (ν n U)) =ᶠ[atTop]
          (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n U)) := by
      filter_upwards [heq] with n hn
      rw [hn]
    rwa [← liminf_congr hfun] at hlb
  · intro F hF
    have hub := h.upper_bound F hF
    have hfun :
        (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (ν n F)) =ᶠ[atTop]
          (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n F)) := by
      filter_upwards [heq] with n hn
      rw [hn]
    rwa [← limsup_congr hfun] at hub

/-- Under Continuous + Giry-Measurable barycenter on raw `ProbabilityMeasure`, Sanov
contracts to the empirical-mean LDP with rate `cramerRateFromSanov`. This is the
Sanov-mean `hLDP` half used by residual wrappers such as
`cramer_theorem_of_HasFiniteMGF_of_forall_bddAbove_of_meanSanovLDP`.
The public `(hMGF)(hbdd)` entry lives in
`Lemma.Random.SatisfiesLDP_EmpiricalMeanLawPi.of.HasFiniteMGF.ForallBddAbove`.

**Residual.** Continuous barycenter on all of `ProbabilityMeasure (ℝᵈ)` is false
without moment restrictions; replace Cont/Meas by truncation
(`satisfiesLDP_map_integral_radialClamp`) + R→∞ exponential equivalence under
`HasFiniteMGF`, or by exp-tightness into a sequential `UniformExpMoment` ball. -/
theorem satisfiesLDP_empiricalMeanLawPi_cramerRateFromSanov_of_continuous_barycenter
    {d : ℕ} (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hbaryCont : Continuous (barycenter : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) → _))
    (hbaryMeas : Measurable (barycenter : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) → _))
    (hJ : LowerSemicontinuous (cramerRateFromSanov μ₀)) :
    SatisfiesLDP (fun n => empiricalMeanLawPi μ₀ n) (cramerRateFromSanov μ₀) := by
  let sanovLaw : ℕ → Measure (ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) := fun n =>
    Measure.map
      (fun ω : Fin n → EuclideanSpace ℝ (Fin d) =>
        if hn : 0 < n then empiricalProbabilityMeasure hn ω
        else μ₀.toProbabilityMeasure)
      (Measure.pi fun _ : Fin n => μ₀)
  have hSanov :
      SatisfiesLDP sanovLaw
        (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
          klDiv (ν : Measure _) μ₀) :=
    satisfiesLDP_sanov_empiricalProbabilityMeasure (μ₀ := μ₀)
  have hJ' : LowerSemicontinuous
      (contractedRate
        (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
          klDiv (ν : Measure _) μ₀)
        barycenter) := by
    convert hJ using 1
    funext y
    rfl
  have hContr :
      SatisfiesLDP (fun n => (sanovLaw n).map barycenter)
        (contractedRate
          (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
            klDiv (ν : Measure _) μ₀)
          barycenter) :=
    satisfiesLDP_map_of_continuous_of_measurable hSanov barycenter
      hbaryCont hbaryMeas hJ'
  refine satisfiesLDP_congr_eventually (by
    convert hContr using 1
    funext y
    rfl) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  dsimp [sanovLaw]
  simpa [hn, ↓reduceDIte] using
    (empiricalMeanLawPi_eq_map_barycenter (μ := μ₀) hn hbaryMeas).symm

/-- Fixed-R truncated empirical-mean LDP via continuous+measurable clamp (no Cont barycenter).
Rate is the Sanov rate contracted through `∫ radialClamp R`. Residual: R→∞ identification
with `cramerRateFromSanov` / true mean under `HasFiniteMGF`. -/
theorem satisfiesLDP_empiricalClampMean_of_HasFiniteMGF
    {d : ℕ} (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    {R : ℝ} (hR : 0 < R)
    (hJ : LowerSemicontinuous
      (contractedRate
        (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
          klDiv (ν : Measure _) μ₀)
        (fun ν => ∫ x, radialClamp R x ∂ν.toMeasure))) :
    SatisfiesLDP
      (fun n =>
        (Measure.map
          (fun ω : Fin n → EuclideanSpace ℝ (Fin d) =>
            if hn : 0 < n then empiricalProbabilityMeasure hn ω
            else μ₀.toProbabilityMeasure)
          (Measure.pi fun _ : Fin n => μ₀)).map
          (fun ν => ∫ x, radialClamp R x ∂ν.toMeasure))
      (contractedRate
        (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
          klDiv (ν : Measure _) μ₀)
        (fun ν => ∫ x, radialClamp R x ∂ν.toMeasure)) :=
  satisfiesLDP_map_integral_radialClamp hR
    (satisfiesLDP_sanov_empiricalProbabilityMeasure (μ₀ := μ₀)) hJ


/-! ### R→∞ clamp residual under HasFiniteMGF (toward hLDP)

Under `HasFiniteMGF`, `E[exp(c ‖x‖)] < ∞` for every `c`. The pointwise clamp residual
equals `0` on the ball and `‖x‖ - R` outside, hence is dominated by `‖x‖` / integrable
exp-norm tails — the analytic half of exponentially good mean↔clamp approximations.

**UniformExpMoment Sanov-tightness is NOT free from `HasFiniteMGF` / `forall_bddAbove`.**
Chernoff into `{ν : ∫ exp((2c)‖x‖) ≤ M}` needs `E[exp(t · exp(c ‖X‖))] < ∞`
(double-exponential). Nondegenerate Gaussians satisfy `HasFiniteMGF + forall_bddAbove`
but not double-exp moments. See `HasFiniteDoubleExpMoment`. That is a strictly
stronger named hyp Random may add; it is not the public `ForallBddAbove` gate.
-/

/-- Clamp residual: `0` on the ball, `‖x‖ - R` outside. -/
theorem norm_sub_radialClamp_eq {d : ℕ}
    {R : ℝ} (hR : 0 ≤ R) (x : EuclideanSpace ℝ (Fin d)) :
    ‖x - radialClamp R x‖ = if ‖x‖ ≤ R then 0 else ‖x‖ - R := by
  by_cases hx : ‖x‖ ≤ R
  · rw [ite_eq_left hx, radialClamp_of_norm_le hR hx, sub_self, norm_zero]
  · have hx' : R < ‖x‖ := lt_of_not_ge hx
    have hx0 : x ≠ 0 := by
      intro h; subst h; simp [norm_zero] at hx'
      exact (not_lt.mpr hR) hx'
    rw [ite_eq_right hx]
    -- ‖x - clamp‖² = ‖x‖² + ‖clamp‖² - 2⟪x,clamp⟫; or direct from formula
    unfold radialClamp
    have hsup : R ⊔ ‖x‖ = ‖x‖ := sup_eq_right.mpr hx'.le
    rw [hsup]
    set a : ℝ := R * ‖x‖⁻¹
    have ha0 : 0 ≤ a := mul_nonneg hR (inv_nonneg.mpr (norm_nonneg _))
    have ha1 : a ≤ 1 := by
      have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      exact (mul_inv_le_iff₀ hpos).mpr (by simpa [mul_one] using hx'.le)
    have hsmul : x - a • x = (1 - a) • x := by
      rw [sub_smul, one_smul]
    change ‖x - a • x‖ = ‖x‖ - R
    rw [hsmul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ha1)]
    have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    calc (1 - a) * ‖x‖ = ‖x‖ - a * ‖x‖ := by ring
      _ = ‖x‖ - R * ‖x‖⁻¹ * ‖x‖ := rfl
      _ = ‖x‖ - R := by field_simp [hpos.ne']

/-- `‖x - clamp R x‖ ≤ ‖x‖`. -/
theorem norm_sub_radialClamp_le_norm' {d : ℕ}
    {R : ℝ} (hR : 0 ≤ R) (x : EuclideanSpace ℝ (Fin d)) :
    ‖x - radialClamp R x‖ ≤ ‖x‖ := by
  rw [norm_sub_radialClamp_eq hR x]
  split_ifs
  · exact norm_nonneg _
  · exact sub_le_self _ hR

/-- Product-space sample mean. -/
noncomputable def sampleMeanPi {d n : ℕ}
    (ω : Fin n → EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (n : ℝ)⁻¹ • ∑ i : Fin n, ω i

/-- Product-space truncated sample mean. -/
noncomputable def sampleClampMeanPi {d n : ℕ} (R : ℝ)
    (ω : Fin n → EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (n : ℝ)⁻¹ • ∑ i : Fin n, radialClamp R (ω i)

theorem dist_sampleMean_sampleClampMean_le {d n : ℕ} {R : ℝ}
    (_hR : 0 ≤ R) (_hn : 0 < n)
    (ω : Fin n → EuclideanSpace ℝ (Fin d)) :
    dist (sampleMeanPi (d := d) (n := n) ω) (sampleClampMeanPi (d := d) (n := n) R ω) ≤
      (n : ℝ)⁻¹ * ∑ i : Fin n, ‖ω i - radialClamp R (ω i)‖ := by
  have h :
      sampleMeanPi (d := d) (n := n) ω - sampleClampMeanPi (d := d) (n := n) R ω =
        (n : ℝ)⁻¹ • ∑ i : Fin n, (ω i - radialClamp R (ω i)) := by
    simp only [sampleMeanPi, sampleClampMeanPi]
    rw [← smul_sub, Finset.sum_sub_distrib]
  rw [dist_eq_norm, h, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- Double-exponential moment: strictly stronger than `HasFiniteMGF`.
Required for Chernoff/Sanov exp-tightness into a fixed `UniformExpMoment` ball.
Not implied by `HasFiniteMGF` or `forall_bddAbove` (counterexample: nondegenerate
Gaussians). -/
def HasFiniteDoubleExpMoment {d : ℕ} (μ₀ : Measure (EuclideanSpace ℝ (Fin d)))
    (c t : ℝ) : Prop :=
  Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (t * Real.exp (c * ‖x‖))) μ₀

/-- Named residual for the Sanov→mean LDP (`hLDP`).

Packaging under `HasFiniteMGF`:
* fixed-R clamp means satisfy LDP via
  `satisfiesLDP_empiricalClampMean_of_HasFiniteMGF`
  (Cont+Meas of the clamp-barycenter map);
* `eventually_uniform_clamp_approx` gives pointwise residual → 0 as R → ∞,
  but a fixed-R mean↔clamp pair is not exp-equivalent (rate stays finite).
Remaining gap: Dembo–Zeitouni 4.2.16 R→∞ exp-good approximation transferring
`contractedRate klDiv clamp_R` → `cramerRateFromSanov` (needs Γ-limit of rates
or a uniform-in-n residual Chernoff bound). That Chernoff step is not yet
internalized; the identity `norm_sub_radialClamp_eq` and
`dist_sampleMean_sampleClampMean_le` are ready for it.

UniformExpMoment / Sanov exp-tightness needs `HasFiniteDoubleExpMoment`,
strictly stronger than `HasFiniteMGF` and not implied by `forall_bddAbove`
(counterexample: nondegenerate Gaussians). -/
def HasEmpiricalMeanSanovLDP {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  SatisfiesLDP (fun n => empiricalMeanLawPi μ₀ n) (cramerRateFromSanov μ₀)

theorem satisfiesLDP_empiricalMeanLawPi_of_HasEmpiricalMeanSanovLDP {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d)))
    (h : HasEmpiricalMeanSanovLDP μ₀) :
    SatisfiesLDP (fun n => empiricalMeanLawPi μ₀ n) (cramerRateFromSanov μ₀) :=
  h

/-- Residual: `HasFiniteMGF` + `forall_bddAbove` + named `HasEmpiricalMeanSanovLDP`.
Public `(hMGF)(hbdd)` entry (no explicit `hLDP`) is the Lemma
`SatisfiesLDP_EmpiricalMeanLawPi.of.HasFiniteMGF.ForallBddAbove`. -/
theorem cramer_theorem_of_HasFiniteMGF_of_forall_bddAbove_of_HasEmpiricalMeanSanovLDP
    {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t))
    (hLDP : HasEmpiricalMeanSanovLDP μ₀) :
    SatisfiesLDP (fun n => empiricalMeanLawPi μ₀ n)
      (cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀) :=
  cramer_theorem_of_HasFiniteMGF_of_forall_bddAbove_of_meanSanovLDP μ₀ hMGF hbdd hLDP

/-! ### R→∞ Chernoff residual (scalar path; no `Continuous.sub` on `E`)

Under `HasFiniteMGF`, `‖x - clamp_R x‖ = (‖x‖ - R)⁺` is ℝ-continuous, dominated by
`‖x‖`, and `∫ exp(λ · residual_R) → 1` as `R → ∞` by Filter-DCT. Chernoff on the
product space then yields Dembo–Zeitouni exponentially-good approximation:
`lim_R limsup_n (1/n) log P(‖mean - clampMean_R‖ > ε) = -∞`.

**Remaining gap for hLDP:** the Atlas/Mathlib-side transfer theorem that upgrades
(exp-good approx of mean by clampMean_R) + (LDP for each clampMean_R) into
`SatisfiesLDP empiricalMeanLawPi (cramerRateFromSanov μ₀)`, which also needs
Γ-convergence of `contractedRate klDiv (∫ clamp_R)` → `cramerRateFromSanov`
(Dembo–Zeitouni 4.2.16). Not leaving unfinished goals; Random may still use
`HasEmpiricalMeanSanovLDP` until that transfer lands.
-/

/-- Scalar form of the clamp residual. -/
theorem norm_sub_radialClamp_eq_posPart {d : ℕ}
    {R : ℝ} (hR : 0 ≤ R) (x : EuclideanSpace ℝ (Fin d)) :
    ‖x - radialClamp R x‖ = (‖x‖ - R)⁺ := by
  rw [norm_sub_radialClamp_eq hR x, posPart_def]
  change (if ‖x‖ ≤ R then (0 : ℝ) else ‖x‖ - R) = max (‖x‖ - R) 0
  split_ifs with hx
  · exact (max_eq_right (sub_nonpos.mpr hx)).symm
  · exact (max_eq_left (le_of_lt (sub_pos.mpr (lt_of_not_ge hx)))).symm

/-- Continuity of the scalar residual via `(‖·‖ - R)⁺` (avoids `Continuous.sub` on `E`). -/
theorem continuous_norm_sub_radialClamp {d : ℕ} {R : ℝ} (hR : 0 ≤ R) :
    Continuous fun x : EuclideanSpace ℝ (Fin d) => ‖x - radialClamp R x‖ := by
  have h : (fun x : EuclideanSpace ℝ (Fin d) => ‖x - radialClamp R x‖) =
      fun x => (‖x‖ - R)⁺ := funext fun x => norm_sub_radialClamp_eq_posPart hR x
  rw [h]
  exact (continuous_norm.sub (continuous_const (y := R))).max continuous_const

/-- `exp(λ · residual)` is integrable under `HasFiniteMGF` for `λ ≥ 0`. -/
theorem integrable_exp_mul_norm_sub_radialClamp_of_HasFiniteMGF {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀) {R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      Real.exp (t * ‖x - radialClamp R x‖)) μ₀ := by
  refine Integrable.mono' (hMGF.integrable_exp_mul_norm t)
    ((Real.continuous_exp.comp (continuous_const.mul
      (continuous_norm_sub_radialClamp hR))).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  have hle : ‖x - radialClamp R x‖ ≤ ‖x‖ := norm_sub_radialClamp_le_norm' hR x
  have : Real.exp (t * ‖x - radialClamp R x‖) ≤ Real.exp (t * ‖x‖) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hle ht)
  simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using this

/-- Pointwise: residual → 0 as `R → ∞`, hence `exp(λ · residual) → 1`. -/
theorem tendsto_exp_mul_norm_sub_radialClamp_atTop {d : ℕ}
    (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    Tendsto (fun R : ℝ => Real.exp (t * ‖x - radialClamp R x‖)) atTop (nhds 1) := by
  have hEv : (fun R : ℝ => Real.exp (t * ‖x - radialClamp R x‖)) =ᶠ[atTop]
      fun _ => (1 : ℝ) := by
    filter_upwards [eventually_ge_atTop ‖x‖] with R hR
    have hR0 : 0 ≤ R := (norm_nonneg x).trans hR
    have hzero : ‖x - radialClamp R x‖ = 0 := by
      rw [norm_sub_radialClamp_eq hR0 x, ite_eq_left hR]
    simp [hzero]
  exact tendsto_const_nhds.congr' hEv.symm

/-- Filter-DCT: `∫ exp(λ · residual_R) → 1` as `R → ∞` under `HasFiniteMGF`, `λ ≥ 0`. -/
theorem tendsto_integral_exp_mul_norm_sub_radialClamp_atTop {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun R : ℝ =>
        ∫ x : EuclideanSpace ℝ (Fin d), Real.exp (t * ‖x - radialClamp R x‖) ∂μ₀)
      atTop (nhds 1) := by
  have hbound_int : Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (t * ‖x‖)) μ₀ :=
    hMGF.integrable_exp_mul_norm t
  have hlim :=
    tendsto_integral_filter_of_dominated_convergence
      (α := EuclideanSpace ℝ (Fin d)) (G := ℝ) (μ := μ₀)
      (l := (atTop : Filter ℝ))
      (F := fun (R : ℝ) x => Real.exp (t * ‖x - radialClamp R x‖))
      (f := fun _ : EuclideanSpace ℝ (Fin d) => (1 : ℝ))
      (bound := fun x => Real.exp (t * ‖x‖))
      ?meas ?bound hbound_int ?pt
  · have h1 : (∫ _ : EuclideanSpace ℝ (Fin d), (1 : ℝ) ∂μ₀) = 1 := by
      simp [MeasureTheory.integral_const, measure_univ]
    exact h1 ▸ hlim
  case meas =>
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact (Real.continuous_exp.comp
      (continuous_const.mul (continuous_norm_sub_radialClamp hR))).aestronglyMeasurable
  case bound =>
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    refine Eventually.of_forall fun x => ?_
    have hle : ‖x - radialClamp R x‖ ≤ ‖x‖ := norm_sub_radialClamp_le_norm' hR x
    have : Real.exp (t * ‖x - radialClamp R x‖) ≤ Real.exp (t * ‖x‖) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hle ht)
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using this
  case pt =>
    exact Eventually.of_forall fun x =>
      tendsto_exp_mul_norm_sub_radialClamp_atTop (d := d) x t

/-- MGF of the residual average factors as a power under the product measure. -/
theorem integral_exp_mul_sum_norm_sub_radialClamp_eq_pow {d n : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t) (hMGF : HasFiniteMGF μ₀) :
    (∫ ω : Fin n → EuclideanSpace ℝ (Fin d),
        Real.exp (t * ∑ i : Fin n, ‖ω i - radialClamp R (ω i)‖)
        ∂Measure.pi fun _ : Fin n => μ₀) =
      (∫ x : EuclideanSpace ℝ (Fin d),
        Real.exp (t * ‖x - radialClamp R x‖) ∂μ₀) ^ n := by
  have hfun :
      (fun ω : Fin n → EuclideanSpace ℝ (Fin d) =>
        Real.exp (t * ∑ i : Fin n, ‖ω i - radialClamp R (ω i)‖)) =
      (fun ω => ∏ i : Fin n, Real.exp (t * ‖ω i - radialClamp R (ω i)‖)) := by
    funext ω
    rw [Finset.mul_sum, Real.exp_sum]
  rw [hfun]
  simpa [Fintype.card_fin] using
    (integral_fintype_prod_eq_pow
      (ι := Fin n) (μ := μ₀)
      (fun x : EuclideanSpace ℝ (Fin d) =>
        Real.exp (t * ‖x - radialClamp R x‖)))


/-- Chernoff: product-space tail of the residual average. -/
theorem measureReal_sum_norm_sub_radialClamp_ge_le {d n : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀) {R t ε : ℝ}
    (hR : 0 ≤ R) (ht : 0 ≤ t) (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin n => μ₀).real
        {ω : Fin n → EuclideanSpace ℝ (Fin d) |
          ε ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, ‖ω i - radialClamp R (ω i)‖} ≤
      Real.exp (-t * ε * n) *
        (∫ x : EuclideanSpace ℝ (Fin d),
          Real.exp (t * ‖x - radialClamp R x‖) ∂μ₀) ^ n := by
  by_cases hn : n = 0
  · subst hn
    simp
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  let μπ : Measure (Fin n → EuclideanSpace ℝ (Fin d)) := Measure.pi fun _ => μ₀
  haveI : IsProbabilityMeasure μπ := by
    dsimp [μπ]; infer_instance
  let X : (Fin n → EuclideanSpace ℝ (Fin d)) → ℝ := fun ω =>
    ∑ i : Fin n, ‖ω i - radialClamp R (ω i)‖
  have hintX : Integrable (fun ω => Real.exp (t * X ω)) μπ := by
    have h :
        Integrable
          (fun ω : Fin n → EuclideanSpace ℝ (Fin d) =>
            ∏ i : Fin n, Real.exp (t * ‖ω i - radialClamp R (ω i)‖))
          (Measure.pi fun _ : Fin n => μ₀) :=
      Integrable.fintype_prod
        (f := fun _ : Fin n => fun x : EuclideanSpace ℝ (Fin d) =>
          Real.exp (t * ‖x - radialClamp R x‖))
        (fun _ => integrable_exp_mul_norm_sub_radialClamp_of_HasFiniteMGF hMGF hR ht)
    have h' : Integrable (fun ω => Real.exp (t * X ω))
        (Measure.pi fun _ : Fin n => μ₀) :=
      h.congr (Eventually.of_forall fun ω => by
        dsimp [X]; rw [Finset.mul_sum, Real.exp_sum])
    simpa [μπ] using h'
  have hchernoff :=
    measure_ge_le_exp_mul_mgf (μ := μπ) (X := X) (t := t) (ε := (n : ℝ) * ε)
      ht hintX
  have hset :
      {ω : Fin n → EuclideanSpace ℝ (Fin d) |
          ε ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, ‖ω i - radialClamp R (ω i)‖} =
        {ω | (n : ℝ) * ε ≤ X ω} := by
    ext ω
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
    constructor
    · intro h
      have := mul_le_mul_of_nonneg_left h hnpos.le
      rwa [← mul_assoc, mul_inv_cancel₀ hnpos.ne', one_mul] at this
    · intro h
      have := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hnpos.le)
      rwa [← mul_assoc, inv_mul_cancel₀ hnpos.ne', one_mul] at this
  -- rewrite goal via hset and mgf factorization
  have hmgf :
      mgf X μπ t =
        (∫ x : EuclideanSpace ℝ (Fin d),
          Real.exp (t * ‖x - radialClamp R x‖) ∂μ₀) ^ n := by
    dsimp [mgf]
    simpa [X] using
      integral_exp_mul_sum_norm_sub_radialClamp_eq_pow (n := n) hR ht hMGF
  -- adjust: measure_ge uses `{ε ≤ X}` while we have `{(n:ℝ)*ε ≤ X}`
  have hbound := hchernoff
  -- hchernoff: μπ.real {ω | (n:ℝ)*ε ≤ X ω} ≤ exp(-t*(n*ε)) * mgf X μπ t
  calc
    μπ.real {ω | ε ≤ (n : ℝ)⁻¹ * ∑ i, ‖ω i - radialClamp R (ω i)‖}
        = μπ.real {ω | (n : ℝ) * ε ≤ X ω} := by rw [hset]
    _ ≤ Real.exp (-t * ((n : ℝ) * ε)) * mgf X μπ t := hbound
    _ = Real.exp (-t * ε * n) *
          (∫ x, Real.exp (t * ‖x - radialClamp R x‖) ∂μ₀) ^ n := by
        rw [hmgf]; ring_nf

/-- Mean↔clamp distance is controlled by the residual average, so the same Chernoff
applies to `{dist(mean, clampMean) ≥ ε}`. -/
theorem measureReal_dist_sampleMean_sampleClampMean_ge_le {d n : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀) {R t ε : ℝ}
    (hR : 0 ≤ R) (hn : 0 < n) (ht : 0 ≤ t) (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin n => μ₀).real
        {ω : Fin n → EuclideanSpace ℝ (Fin d) |
          ε ≤ dist (sampleMeanPi (d := d) (n := n) ω)
            (sampleClampMeanPi (d := d) (n := n) R ω)} ≤
      Real.exp (-t * ε * n) *
        (∫ x : EuclideanSpace ℝ (Fin d),
          Real.exp (t * ‖x - radialClamp R x‖) ∂μ₀) ^ n := by
  have hsub :
      {ω : Fin n → EuclideanSpace ℝ (Fin d) |
          ε ≤ dist (sampleMeanPi (d := d) (n := n) ω)
            (sampleClampMeanPi (d := d) (n := n) R ω)} ⊆
        {ω | ε ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, ‖ω i - radialClamp R (ω i)‖} := by
    intro ω hω
    exact hω.trans (dist_sampleMean_sampleClampMean_le (d := d) (n := n) hR hn ω)
  refine le_trans ?_ (measureReal_sum_norm_sub_radialClamp_ge_le
    (d := d) (n := n) hMGF hR ht hε)
  exact measureReal_mono hsub


/-- ENNReal form of the mean↔clamp Chernoff bound. -/
theorem measure_dist_sampleMean_sampleClampMean_ge_le_exp {d n : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀) {R t ε : ℝ}
    (hR : 0 ≤ R) (hn : 0 < n) (ht : 0 ≤ t) (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin n => μ₀)
        {ω : Fin n → EuclideanSpace ℝ (Fin d) |
          ε ≤ dist (sampleMeanPi (d := d) (n := n) ω)
            (sampleClampMeanPi (d := d) (n := n) R ω)} ≤
      ENNReal.ofReal
        (Real.exp (-t * ε * n) *
          (∫ x : EuclideanSpace ℝ (Fin d),
            Real.exp (t * ‖x - radialClamp R x‖) ∂μ₀) ^ n) := by
  have hreal :=
    measureReal_dist_sampleMean_sampleClampMean_ge_le
      (d := d) (n := n) hMGF hR hn ht hε
  set s :=
    {ω : Fin n → EuclideanSpace ℝ (Fin d) |
      ε ≤ dist (sampleMeanPi (d := d) (n := n) ω)
        (sampleClampMeanPi (d := d) (n := n) R ω)}
  have hfin : (Measure.pi fun _ : Fin n => μ₀) s ≠ ∞ := measure_ne_top _ _
  have hpos :
      0 ≤ Real.exp (-t * ε * n) *
        (∫ x : EuclideanSpace ℝ (Fin d),
          Real.exp (t * ‖x - radialClamp R x‖) ∂μ₀) ^ n := by positivity
  calc
    (Measure.pi fun _ : Fin n => μ₀) s
        = ENNReal.ofReal ((Measure.pi fun _ : Fin n => μ₀).real s) :=
          (ENNReal.ofReal_toReal hfin).symm
    _ ≤ ENNReal.ofReal
          (Real.exp (-t * ε * n) *
            (∫ x, Real.exp (t * ‖x - radialClamp R x‖) ∂μ₀) ^ n) :=
          (ENNReal.ofReal_le_ofReal_iff hpos).mpr hreal

/-! ### Dembo–Zeitouni exp-good approximation rate → -∞ -/

/-- Real form of Dembo–Zeitouni exp-good approximation: for every `ε, δ > 0` there is
`R₀` such that for all `R ≥ R₀` and `n > 0`,
`P(dist(mean, clampMean_R) ≥ ε) ≤ exp(-δ n)`.
Obtained from Chernoff + Filter-DCT residual mgf → 1 under `HasFiniteMGF`. -/
theorem exists_radius_expGood_sampleMean_sampleClampMean {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ n : ℕ, 0 < n →
      (Measure.pi fun _ : Fin n => μ₀).real
          {ω : Fin n → EuclideanSpace ℝ (Fin d) |
            ε ≤ dist (sampleMeanPi (d := d) (n := n) ω)
              (sampleClampMeanPi (d := d) (n := n) R ω)} ≤
        Real.exp (-δ * n) := by
  set t : ℝ := (δ + 1) / ε
  have ht : 0 < t := div_pos (add_pos_of_pos_of_nonneg hδ zero_le_one) hε
  have htend := tendsto_integral_exp_mul_norm_sub_radialClamp_atTop hMGF ht.le
  have hnhds : ∀ᶠ R : ℝ in atTop,
      ∫ x : EuclideanSpace ℝ (Fin d), Real.exp (t * ‖x - radialClamp R x‖) ∂μ₀ <
        Real.exp 1 := by
    have : {y : ℝ | y < Real.exp 1} ∈ nhds (1 : ℝ) :=
      isOpen_Iio.mem_nhds (by simp [Real.one_lt_exp_iff])
    exact htend this
  have hEv : ∀ᶠ R : ℝ in atTop,
      0 ≤ R ∧
        ∫ x : EuclideanSpace ℝ (Fin d), Real.exp (t * ‖x - radialClamp R x‖) ∂μ₀ <
          Real.exp 1 := by
    filter_upwards [eventually_ge_atTop (0 : ℝ), hnhds] with R hR0 hM
    exact ⟨hR0, hM⟩
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.mp hEv
  refine ⟨R₀, (hR₀ R₀ le_rfl).1, fun R hRge n hn => ?_⟩
  have hR0 : 0 ≤ R := (hR₀ R₀ le_rfl).1.trans hRge
  set M : ℝ :=
    ∫ x : EuclideanSpace ℝ (Fin d), Real.exp (t * ‖x - radialClamp R x‖) ∂μ₀
  have hMlt : M < Real.exp 1 := (hR₀ R hRge).2
  have hMge1 : (1 : ℝ) ≤ M := by
    have hpt : ∀ x : EuclideanSpace ℝ (Fin d), (1 : ℝ) ≤ Real.exp (t * ‖x - radialClamp R x‖) := fun x => by
      have hnn : 0 ≤ ‖x - radialClamp R x‖ := norm_nonneg (x - radialClamp R x)
      have : 0 ≤ t * ‖x - radialClamp R x‖ := mul_nonneg ht.le hnn
      simpa [Real.exp_zero] using Real.one_le_exp this
    have h1 :=
      integral_mono (integrable_const (1 : ℝ))
        (integrable_exp_mul_norm_sub_radialClamp_of_HasFiniteMGF hMGF hR0 ht.le) hpt
    simpa [integral_const, measure_univ] using h1
  have hchern :=
    measureReal_dist_sampleMean_sampleClampMean_ge_le
      (d := d) (n := n) hMGF hR0 hn ht.le hε.le
  have htε : t * ε = δ + 1 := div_mul_cancel₀ _ hε.ne'
  have hMpos : 0 ≤ M := le_trans (by norm_num : (0 : ℝ) ≤ 1) hMge1
  -- P ≤ exp(-tε·n)·Mⁿ ≤ exp(-tε·n)·(exp 1)ⁿ = exp((-tε+1)·n) = exp(-δ·n)
  have hstep1 :
      Real.exp (-t * ε * n) * M ^ n ≤
        Real.exp (-t * ε * n) * (Real.exp 1) ^ n := by
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
    exact pow_le_pow_left₀ hMpos hMlt.le n
  have hstep2 :
      Real.exp (-t * ε * n) * (Real.exp 1) ^ n = Real.exp ((-t * ε + 1) * n) := by
    have h1n : (Real.exp 1) ^ n = Real.exp (n : ℝ) := by
      rw [← Real.exp_nsmul, nsmul_eq_mul, mul_one]
    rw [h1n, ← Real.exp_add]
    congr 1
    ring
  have hstep3 : (-t * ε + 1) * n = -δ * n := by
    have : -t * ε + 1 = -δ := by
      calc -t * ε + 1 = -(t * ε) + 1 := by ring
        _ = -(δ + 1) + 1 := by rw [htε]
        _ = -δ := by ring
    rw [this]
  calc
    (Measure.pi fun _ : Fin n => μ₀).real
        {ω : Fin n → EuclideanSpace ℝ (Fin d) |
          ε ≤ dist (sampleMeanPi (d := d) (n := n) ω)
            (sampleClampMeanPi (d := d) (n := n) R ω)}
        ≤ Real.exp (-t * ε * n) * M ^ n := hchern
    _ ≤ Real.exp (-t * ε * n) * (Real.exp 1) ^ n := hstep1
    _ = Real.exp ((-t * ε + 1) * n) := hstep2
    _ = Real.exp (-δ * n) := by rw [hstep3]

/-! ### Clamp empirical identification + eventually exp-good

Identification of truncated empirical barycenter with `sampleClampMeanPi`, plus the
Filter form of Dembo–Zeitouni exp-good approximation. Remaining gap for full `hLDP`
documented at the end of this section.
-/

/-- Truncated barycenter of the empirical measure is the truncated sample mean. -/
theorem integral_radialClamp_empiricalProbabilityMeasure {d n : ℕ}
    {R : ℝ} (hR : 0 ≤ R) (hn : 0 < n)
    (ω : Fin n → EuclideanSpace ℝ (Fin d)) :
    (∫ x, radialClamp R x ∂(empiricalProbabilityMeasure hn ω).toMeasure) =
      sampleClampMeanPi (d := d) (n := n) R ω := by
  unfold sampleClampMeanPi empiricalProbabilityMeasure
  change
      (∫ x, radialClamp R x ∂((n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i))) =
        (n : ℝ)⁻¹ • ∑ i : Fin n, radialClamp R (ω i)
  have hinv : ((n : ℝ≥0∞)⁻¹).toReal = (n : ℝ)⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have hdir : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Integrable (fun x : EuclideanSpace ℝ (Fin d) => radialClamp R x)
        (Measure.dirac (ω i)) := by
    intro i _
    exact integrable_dirac (by simp)
  rw [integral_smul_measure, integral_finsetSum_measure hdir, hinv]
  simp [integral_dirac]

/-- Sample mean law is the product pushforward of `sampleMeanPi` (n > 0). -/
theorem empiricalMeanLawPi_eq_map_sampleMeanPi {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) {n : ℕ} (hn : 0 < n) :
    empiricalMeanLawPi μ n =
      (Measure.pi fun _ : Fin n => μ).map (sampleMeanPi (d := d) (n := n)) := by
  simp only [empiricalMeanLawPi, hn, ↓reduceIte]
  rfl

/-- Filter form: for every `ε, δ > 0`, eventually in `R` the Chernoff bound
`P(dist ≥ ε) ≤ exp(-δ n)` holds for all `n > 0`. -/
theorem eventually_expGood_sampleMean_sampleClampMean {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ R : ℝ in atTop,
      0 ≤ R ∧ ∀ n : ℕ, 0 < n →
        (Measure.pi fun _ : Fin n => μ₀).real
            {ω : Fin n → EuclideanSpace ℝ (Fin d) |
              ε ≤ dist (sampleMeanPi (d := d) (n := n) ω)
                (sampleClampMeanPi (d := d) (n := n) R ω)} ≤
          Real.exp (-δ * n) := by
  obtain ⟨R₀, hR₀, hbound⟩ :=
    exists_radius_expGood_sampleMean_sampleClampMean (d := d) hMGF hε hδ
  refine Filter.eventually_atTop.mpr ⟨R₀, fun R hRge => ?_⟩
  exact ⟨hR₀.trans hRge, fun n hn => hbound R hRge n hn⟩

/-- Function form of the truncated-barycenter identification. -/
theorem integral_radialClamp_comp_empiricalProbabilityMeasure {d n : ℕ}
    {R : ℝ} (hR : 0 ≤ R) (hn : 0 < n) :
    (fun ω : Fin n → EuclideanSpace ℝ (Fin d) =>
        ∫ x, radialClamp R x ∂(empiricalProbabilityMeasure hn ω).toMeasure) =
      sampleClampMeanPi (d := d) (n := n) R :=
  funext fun ω => integral_radialClamp_empiricalProbabilityMeasure hR hn ω

/-- Clamp LDP pushforward equals the product pushforward of `sampleClampMeanPi`.
Connects `satisfiesLDP_empiricalClampMean_of_HasFiniteMGF` to the exp-good sample-mean
approximation. -/
theorem map_sanovEmpirical_integral_radialClamp_eq_map_sampleClampMeanPi {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) {n : ℕ} (hn : 0 < n)
    {R : ℝ} (hR : 0 < R) :
    ((Measure.pi fun _ : Fin n => μ).map fun ω =>
          empiricalProbabilityMeasure hn ω).map
        (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
          ∫ x, radialClamp R x ∂ν.toMeasure) =
      (Measure.pi fun _ : Fin n => μ).map
        (sampleClampMeanPi (d := d) (n := n) R) := by
  have hemp : Measurable (fun ω : Fin n → EuclideanSpace ℝ (Fin d) =>
      empiricalProbabilityMeasure hn ω) :=
    Measurable.of.Gt_0 hn
  have hclamp : Measurable
      (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
        ∫ x, radialClamp R x ∂ν.toMeasure) :=
    measurable_integral_radialClamp hR
  rw [Measure.map_map hclamp hemp]
  exact congrArg (fun f => Measure.map f (Measure.pi fun _ : Fin n => μ))
    (integral_radialClamp_comp_empiricalProbabilityMeasure hR.le hn)

/-- Fiber inequality: clamp-contracted rate at the truncated barycenter is ≤ KL. -/
theorem contractedRate_integral_radialClamp_le_klDiv {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d)))
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) {R : ℝ} :
    contractedRate
        (fun ν' : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
          klDiv (ν' : Measure _) μ₀)
        (fun ν' => ∫ x, radialClamp R x ∂ν'.toMeasure)
        (∫ x, radialClamp R x ∂ν.toMeasure) ≤
      klDiv (ν : Measure _) μ₀ :=
  iInf₂_le ν (by simp)

/-- Recovery path: truncated means of a finite-KL fiber tend to its barycenter under
`HasFiniteMGF` (via internalized integrable identity). -/
theorem tendsto_integral_radialClamp_barycenter_of_klDiv_ne_top_of_HasFiniteMGF {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (hne : klDiv (ν : Measure _) μ₀ ≠ ∞) :
    Tendsto (fun n : ℕ => ∫ x, radialClamp ((n : ℝ) + 1) x ∂ν.toMeasure) atTop
      (𝓝 (barycenter ν)) :=
  tendsto_integral_radialClamp_barycenter ν
    (integrable_id_of_klDiv_ne_top_of_HasFiniteMGF μ₀ ν hMGF hne)

/-- Γ-recovery half along the clamp path: for every finite-KL fiber `ν`, the clamp
contracted rate evaluated on the recovery sequence stays ≤ `klDiv ν μ₀`. Combined with
`tendsto_integral_radialClamp_barycenter_of_klDiv_ne_top_of_HasFiniteMGF` this is the
Dembo–Zeitouni recovery ingredient toward `cramerRateFromSanov`. -/
theorem contractedRate_integral_radialClamp_recovery_le_klDiv_of_HasFiniteMGF {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (_hMGF : HasFiniteMGF μ₀)
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (_hne : klDiv (ν : Measure _) μ₀ ≠ ∞) (n : ℕ) :
    contractedRate
        (fun ν' : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
          klDiv (ν' : Measure _) μ₀)
        (fun ν' => ∫ x, radialClamp ((n : ℝ) + 1) x ∂ν'.toMeasure)
        (∫ x, radialClamp ((n : ℝ) + 1) x ∂ν.toMeasure) ≤
      klDiv (ν : Measure _) μ₀ :=
  contractedRate_integral_radialClamp_le_klDiv μ₀ ν

/-! ### Γ-liminf of clamp-contracted rates via clamp DV + Legendre

Avoids KL-compactness: Donsker–Varadhan on the bounded continuous test
`⟪t, radialClamp R ·⟫` lower-bounds `I_R`, then DCT sends the clamp MGF to the
true MGF under `HasFiniteMGF`, and the Legendre envelope recovers
`cramerRateFunction` / `cramerRateFromSanov` (with `forall_bddAbove`).
-/

/-- Clamped linear test obeys Donsker–Varadhan against any probability `ν`. -/
theorem ofReal_integral_inner_radialClamp_sub_log_le_klDiv {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (t : EuclideanSpace ℝ (Fin d)) {R : ℝ} (hR : 0 < R) :
    ENNReal.ofReal
        ((∫ x, ⟪t, radialClamp R x⟫_ℝ ∂ν.toMeasure) -
          Real.log (∫ x, Real.exp (⟪t, radialClamp R x⟫_ℝ) ∂μ₀)) ≤
      klDiv ν.toMeasure μ₀ := by
  by_cases htop : klDiv ν.toMeasure μ₀ = ∞
  · simp [htop]
  · have hpair := klDiv_ne_top_iff.mp htop
    have hDV :
        (∫ x, ⟪t, radialClamp R x⟫_ℝ ∂ν.toMeasure) -
            Real.log (∫ x, Real.exp (⟪t, radialClamp R x⟫_ℝ) ∂μ₀) ≤
          (klDiv ν.toMeasure μ₀).toReal :=
      Integral_Sub_Log_Integral_Exp.le.ToRealKlDiv.of.Any_All_LeAbs.Continuous.Integrable_Llr
        hpair.1 hpair.2 (continuous_inner_radialClamp t hR)
        ⟨‖t‖ * R, fun x => abs_inner_radialClamp_le t hR.le x⟩
    exact ENNReal.ofReal_le_of_le_toReal hDV

/-- Inner product passes inside the Bochner integral of `radialClamp`. -/
theorem integral_inner_radialClamp_eq_inner_integral {d : ℕ}
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (t : EuclideanSpace ℝ (Fin d)) {R : ℝ} (hR : 0 < R) :
    (∫ x, ⟪t, radialClamp R x⟫_ℝ ∂ν.toMeasure) =
      ⟪t, ∫ x, radialClamp R x ∂ν.toMeasure⟫_ℝ := by
  have hint : Integrable (fun x => radialClamp R x) ν.toMeasure :=
    Integrable.mono' (integrable_const (μ := ν.toMeasure) R)
      (continuous_radialClamp hR).aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa using norm_radialClamp_le hR.le x)
  simpa using (innerSL ℝ t).integral_comp_comm hint

/-- Fiber form: Legendre integrand of the clamp MGF ≤ clamp-contracted Sanov rate. -/
theorem ofReal_inner_sub_log_clampMGF_le_contractedRate_integral_radialClamp {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (y t : EuclideanSpace ℝ (Fin d)) {R : ℝ} (hR : 0 < R) :
    ENNReal.ofReal
        (⟪t, y⟫_ℝ -
          Real.log (∫ x, Real.exp (⟪t, radialClamp R x⟫_ℝ) ∂μ₀)) ≤
      contractedRate
        (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
          klDiv (ν : Measure _) μ₀)
        (fun ν => ∫ x, radialClamp R x ∂ν.toMeasure) y := by
  unfold contractedRate
  refine le_iInf₂ fun ν hν => ?_
  have hy : (∫ x, radialClamp R x ∂ν.toMeasure) = y := by
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using hν
  have hDV := ofReal_integral_inner_radialClamp_sub_log_le_klDiv μ₀ ν t hR
  have hinner := integral_inner_radialClamp_eq_inner_integral ν t hR
  simpa [hinner, hy] using hDV

/-- Clamp MGF → true MGF along `R = n+1`, under `HasFiniteMGF`. -/
theorem tendsto_integral_exp_inner_radialClamp_of_HasFiniteMGF {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀) (t : EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun n : ℕ => ∫ x, Real.exp (⟪t, radialClamp ((n : ℝ) + 1) x⟫_ℝ) ∂μ₀) atTop
      (𝓝 (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀)) :=
  tendsto_integral_exp_inner_radialClamp μ₀ t
    (hMGF.integrable_exp_mul_norm ‖t‖) (hMGF t)

/-- Log-clamp-MGF → log-MGF under `HasFiniteMGF`. -/
theorem tendsto_log_integral_exp_inner_radialClamp_of_HasFiniteMGF {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀) (t : EuclideanSpace ℝ (Fin d)) :
    Tendsto
      (fun n : ℕ =>
        Real.log (∫ x, Real.exp (⟪t, radialClamp ((n : ℝ) + 1) x⟫_ℝ) ∂μ₀)) atTop
      (𝓝 (Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀))) := by
  have hexp := hMGF t
  have hpos : 0 < ∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀ := integral_exp_pos hexp
  exact (Real.continuousAt_log hpos.ne').tendsto.comp
    (tendsto_integral_exp_inner_radialClamp_of_HasFiniteMGF hMGF t)

/-- Pointwise Fenchel–Young competitor ≤ liminf of clamp-contracted rates along any
recovery sequence `y_n → y` (R = n+1). -/
theorem liminf_contractedRate_integral_radialClamp_ge_ofReal_fy_of_HasFiniteMGF {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (y : EuclideanSpace ℝ (Fin d)) (t : EuclideanSpace ℝ (Fin d))
    (yseq : ℕ → EuclideanSpace ℝ (Fin d))
    (hy : Tendsto yseq atTop (𝓝 y)) :
    ENNReal.ofReal
        (⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t) ≤
      liminf (fun n : ℕ =>
        contractedRate
          (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
            klDiv (ν : Measure _) μ₀)
          (fun ν => ∫ x, radialClamp ((n : ℝ) + 1) x ∂ν.toMeasure)
          (yseq n)) atTop := by
  have hfy :
      Tendsto
        (fun n : ℕ =>
          ⟪t, yseq n⟫_ℝ -
            Real.log (∫ x, Real.exp (⟪t, radialClamp ((n : ℝ) + 1) x⟫_ℝ) ∂μ₀)) atTop
        (𝓝 (⟪t, y⟫_ℝ - Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀))) := by
    have hinner : Tendsto (fun n : ℕ => ⟪t, yseq n⟫_ℝ) atTop (𝓝 ⟪t, y⟫_ℝ) :=
      ((innerSL ℝ t).continuous.tendsto y).comp hy
    exact hinner.sub (tendsto_log_integral_exp_inner_radialClamp_of_HasFiniteMGF hMGF t)
  have hofReal :
      Tendsto
        (fun n : ℕ =>
          ENNReal.ofReal
            (⟪t, yseq n⟫_ℝ -
              Real.log (∫ x, Real.exp (⟪t, radialClamp ((n : ℝ) + 1) x⟫_ℝ) ∂μ₀))) atTop
        (𝓝
          (ENNReal.ofReal
            (⟪t, y⟫_ℝ - Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀)))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp hfy
  have hle : ∀ n : ℕ,
      ENNReal.ofReal
          (⟪t, yseq n⟫_ℝ -
            Real.log (∫ x, Real.exp (⟪t, radialClamp ((n : ℝ) + 1) x⟫_ℝ) ∂μ₀)) ≤
        contractedRate
          (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
            klDiv (ν : Measure _) μ₀)
          (fun ν => ∫ x, radialClamp ((n : ℝ) + 1) x ∂ν.toMeasure)
          (yseq n) := fun n =>
    ofReal_inner_sub_log_clampMGF_le_contractedRate_integral_radialClamp
      μ₀ (yseq n) t (Nat.cast_add_one_pos n)
  have hliminf :
      liminf
          (fun n : ℕ =>
            ENNReal.ofReal
              (⟪t, yseq n⟫_ℝ -
                Real.log (∫ x, Real.exp (⟪t, radialClamp ((n : ℝ) + 1) x⟫_ℝ) ∂μ₀))) atTop ≤
        liminf
          (fun n : ℕ =>
            contractedRate
              (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
                klDiv (ν : Measure _) μ₀)
              (fun ν => ∫ x, radialClamp ((n : ℝ) + 1) x ∂ν.toMeasure)
              (yseq n)) atTop :=
    liminf_le_liminf (Eventually.of_forall hle)
  have hlogid :
      ⟪t, y⟫_ℝ - Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀) =
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t := by
    simp [logMGFVec_id]
  simpa [hofReal.liminf_eq, hlogid] using hliminf

/-- `cramerRateFunction` ≤ liminf of clamp-contracted rates (Legendre envelope). -/
theorem liminf_contractedRate_integral_radialClamp_ge_cramerRateFunction_of_HasFiniteMGF
    {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (y : EuclideanSpace ℝ (Fin d))
    (hbdd : BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
      ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t))
    (yseq : ℕ → EuclideanSpace ℝ (Fin d))
    (hy : Tendsto yseq atTop (𝓝 y)) :
    cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y ≤
      liminf (fun n : ℕ =>
        contractedRate
          (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
            klDiv (ν : Measure _) μ₀)
          (fun ν => ∫ x, radialClamp ((n : ℝ) + 1) x ∂ν.toMeasure)
          (yseq n)) atTop := by
  refine cramerRateFunction_le_of_forall_ofReal_inner_sub_logMGF_le
    (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y _ hbdd fun t => ?_
  exact liminf_contractedRate_integral_radialClamp_ge_ofReal_fy_of_HasFiniteMGF
    hMGF y t yseq hy

/-- Γ-liminf half: `cramerRateFromSanov` ≤ liminf `I_{n+1}(y_n)` under
`HasFiniteMGF` + `forall_bddAbove` (rate ID). -/
theorem liminf_contractedRate_integral_radialClamp_ge_cramerRateFromSanov_of_HasFiniteMGF_of_forall_bddAbove
    {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t))
    (y : EuclideanSpace ℝ (Fin d))
    (yseq : ℕ → EuclideanSpace ℝ (Fin d))
    (hy : Tendsto yseq atTop (𝓝 y)) :
    cramerRateFromSanov μ₀ y ≤
      liminf (fun n : ℕ =>
        contractedRate
          (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
            klDiv (ν : Measure _) μ₀)
          (fun ν => ∫ x, radialClamp ((n : ℝ) + 1) x ∂ν.toMeasure)
          (yseq n)) atTop := by
  have hcover := TiltCover_of_HasFiniteMGF_of_forall_bddAbove μ₀ hMGF hbdd
  have heq := cramerRateFromSanov_eq_cramerRateFunction_of_tiltCover_no_hid
    μ₀ hMGF hcover hbdd y
  rw [heq]
  exact liminf_contractedRate_integral_radialClamp_ge_cramerRateFunction_of_HasFiniteMGF
    hMGF y (hbdd y) yseq hy

/-- Bundled Γ-convergence ingredients for clamp-contracted rates under
`HasFiniteMGF` + `forall_bddAbove`: recovery path + Legendre Γ-liminf. -/
theorem gamma_contractedRate_integral_radialClamp_of_HasFiniteMGF_of_forall_bddAbove {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t))
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (hne : klDiv (ν : Measure _) μ₀ ≠ ∞) :
    (Tendsto (fun n : ℕ => ∫ x, radialClamp ((n : ℝ) + 1) x ∂ν.toMeasure) atTop
        (𝓝 (barycenter ν))) ∧
      (∀ n : ℕ,
        contractedRate
            (fun ν' : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
              klDiv (ν' : Measure _) μ₀)
            (fun ν' => ∫ x, radialClamp ((n : ℝ) + 1) x ∂ν'.toMeasure)
            (∫ x, radialClamp ((n : ℝ) + 1) x ∂ν.toMeasure) ≤
          klDiv (ν : Measure _) μ₀) ∧
      (∀ yseq : ℕ → EuclideanSpace ℝ (Fin d), Tendsto yseq atTop (𝓝 (barycenter ν)) →
        cramerRateFromSanov μ₀ (barycenter ν) ≤
          liminf (fun n : ℕ =>
            contractedRate
              (fun ν' : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
                klDiv (ν' : Measure _) μ₀)
              (fun ν' => ∫ x, radialClamp ((n : ℝ) + 1) x ∂ν'.toMeasure)
              (yseq n)) atTop) :=
  ⟨tendsto_integral_radialClamp_barycenter_of_klDiv_ne_top_of_HasFiniteMGF hMGF ν hne,
    fun n => contractedRate_integral_radialClamp_recovery_le_klDiv_of_HasFiniteMGF hMGF ν hne n,
    fun yseq hy =>
      liminf_contractedRate_integral_radialClamp_ge_cramerRateFromSanov_of_HasFiniteMGF_of_forall_bddAbove
        hMGF hbdd (barycenter ν) yseq hy⟩

/-! ### Exp-good family as `EventuallyExpGoodApprox` + diagonal readiness -/

/-- Package Chernoff exp-good mean↔clamp as the abstract family predicate. -/
theorem EventuallyExpGoodApprox_sampleMean_sampleClampMean {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀) :
    EventuallyExpGoodApprox
      (fun n : ℕ => Measure.pi fun _ : Fin n => μ₀)
      (fun n : ℕ => sampleMeanPi (d := d) (n := n))
      (fun R : ℝ => fun n : ℕ => sampleClampMeanPi (d := d) (n := n) R) := by
  intro ε hε δ hδ
  filter_upwards [eventually_expGood_sampleMean_sampleClampMean (d := d) hMGF hε hδ] with R hR
  exact hR.2

/-- Along any `R_n → ∞`, sample mean and clamp-mean are exponentially equivalent under
`HasFiniteMGF`. Rate on the clamp side still depends on `R_n` (needs DZ 4.2.16 Γ-passage). -/
theorem ExpEquivalentMaps_sampleMean_sampleClampMean_diagonal {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) :
    ExpEquivalentMaps
      (fun n : ℕ => Measure.pi fun _ : Fin n => μ₀)
      (fun n : ℕ => sampleMeanPi (d := d) (n := n))
      (fun n : ℕ => sampleClampMeanPi (d := d) (n := n) (R n)) :=
  ExpEquivalentMaps_of_EventuallyExpGoodApprox_diagonal
    (fun n => Measure.pi fun _ : Fin n => μ₀)
    (fun n => sampleMeanPi (d := d) (n := n))
    (fun R n => sampleClampMeanPi (d := d) (n := n) R)
    (EventuallyExpGoodApprox_sampleMean_sampleClampMean hMGF) R hR

/-! ### Specialization of DZ 4.2.16 → empirical-mean Sanov LDP -/

/-- Clamp-contracted Sanov rate; for `R ≤ 0` reuse the `R = 1` profile. -/
noncomputable def clampContractedRate {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) (R : ℝ) :
    EuclideanSpace ℝ (Fin d) → ENNReal :=
  fun y =>
    contractedRate
      (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
        klDiv (ν : Measure _) μ₀)
      (fun ν => ∫ x, radialClamp (if 0 < R then R else (1 : ℝ)) x ∂ν.toMeasure)
      y

theorem clampContractedRate_eq_of_pos {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) {R : ℝ} (hR : 0 < R) :
    clampContractedRate μ₀ R =
      contractedRate
        (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
          klDiv (ν : Measure _) μ₀)
        (fun ν => ∫ x, radialClamp R x ∂ν.toMeasure) := by
  funext y; simp [clampContractedRate, hR]

/-- Product-space clamp map paired with `clampContractedRate`. -/
noncomputable def sampleClampMeanPi' {d n : ℕ} (R : ℝ)
    (ω : Fin n → EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  sampleClampMeanPi (d := d) (n := n) (if 0 < R then R else (1 : ℝ)) ω

theorem sampleClampMeanPi'_eq_of_pos {d n : ℕ} {R : ℝ} (hR : 0 < R) :
    sampleClampMeanPi' (d := d) (n := n) R =
      sampleClampMeanPi (d := d) (n := n) R := by
  funext ω; simp [sampleClampMeanPi', hR]

theorem sampleClampMeanPi'_eq_of_nonpos {d n : ℕ} {R : ℝ} (hR : ¬ 0 < R) :
    sampleClampMeanPi' (d := d) (n := n) R =
      sampleClampMeanPi (d := d) (n := n) 1 := by
  funext ω; simp [sampleClampMeanPi', hR]

theorem measurable_sampleMeanPi {d n : ℕ} :
    Measurable (sampleMeanPi (d := d) (n := n)) := by
  unfold sampleMeanPi
  exact (measurable_const_smul _).comp (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)

theorem measurable_sampleClampMeanPi_of_pos {d n : ℕ} {R : ℝ} (hR : 0 < R) :
    Measurable (sampleClampMeanPi (d := d) (n := n) R) := by
  unfold sampleClampMeanPi
  have hc : Measurable (radialClamp (E := EuclideanSpace ℝ (Fin d)) R) :=
    (continuous_radialClamp hR).measurable
  exact (measurable_const_smul _).comp
    (Finset.measurable_sum _ fun i _ => hc.comp (measurable_pi_apply i))

theorem measurable_sampleClampMeanPi' {d n : ℕ} (R : ℝ) :
    Measurable (sampleClampMeanPi' (d := d) (n := n) R) := by
  by_cases hR : 0 < R
  · rw [sampleClampMeanPi'_eq_of_pos (d := d) (n := n) hR]
    exact measurable_sampleClampMeanPi_of_pos (d := d) (n := n) hR
  · rw [sampleClampMeanPi'_eq_of_nonpos (d := d) (n := n) hR]
    exact measurable_sampleClampMeanPi_of_pos (d := d) (n := n) one_pos

/-- Exp-good approx with the positive-radius clamp family `sampleClampMeanPi'`. -/
theorem EventuallyExpGoodApprox_sampleMean_sampleClampMeanPi' {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀) :
    EventuallyExpGoodApprox
      (fun n : ℕ => Measure.pi fun _ : Fin n => μ₀)
      (fun n : ℕ => sampleMeanPi (d := d) (n := n))
      (fun R : ℝ => fun n : ℕ => sampleClampMeanPi' (d := d) (n := n) R) := by
  intro ε hε δ hδ
  filter_upwards [eventually_expGood_sampleMean_sampleClampMean (d := d) hMGF hε hδ,
    eventually_gt_atTop (0 : ℝ)] with R hGood hRpos
  intro n hn
  simpa [sampleClampMeanPi'_eq_of_pos (d := d) (n := n) hRpos] using hGood.2 n hn

/-- Γ-liminf along `R = n+1` toward `cramerRateFromSanov`. -/
theorem GammaLiminf_clampContractedRate_cramerRateFromSanov
    {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t)) :
    GammaLiminf
      (fun n : ℕ => clampContractedRate μ₀ ((n : ℝ) + 1))
      (cramerRateFromSanov μ₀) := by
  intro y yseq hy
  have heq : ∀ n : ℕ,
      clampContractedRate μ₀ ((n : ℝ) + 1) (yseq n) =
        contractedRate
          (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
            klDiv (ν : Measure _) μ₀)
          (fun ν => ∫ x, radialClamp ((n : ℝ) + 1) x ∂ν.toMeasure)
          (yseq n) := by
    intro n
    rw [clampContractedRate_eq_of_pos μ₀ (Nat.cast_add_one_pos n)]
  simp_rw [heq]
  exact liminf_contractedRate_integral_radialClamp_ge_cramerRateFromSanov_of_HasFiniteMGF_of_forall_bddAbove
    hMGF hbdd y yseq hy

/-- Bound-only open lower bound for clamp pushforwards at fixed `R > 0`. -/
theorem liminf_log_map_sampleClampMeanPi_ge_iInf_clampContractedRate {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    {R : ℝ} (hR : 0 < R) {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) :
    - (⨅ y ∈ U, (clampContractedRate μ₀ R y : EReal)) ≤
      liminf (fun n => ((n : ℕ) : EReal)⁻¹ *
        ENNReal.log
          ((Measure.pi fun _ : Fin n => μ₀).map
            (sampleClampMeanPi (d := d) (n := n) R) U)) atTop := by
  let sanovLaw : ℕ → Measure (ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) := fun n =>
    Measure.map
      (fun ω : Fin n → EuclideanSpace ℝ (Fin d) =>
        if hn : 0 < n then empiricalProbabilityMeasure hn ω
        else μ₀.toProbabilityMeasure)
      (Measure.pi fun _ : Fin n => μ₀)
  have hSanov :
      SatisfiesLDP sanovLaw
        (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
          klDiv (ν : Measure _) μ₀) :=
    satisfiesLDP_sanov_empiricalProbabilityMeasure (μ₀ := μ₀)
  have hbound := liminf_log_map_ge_iInf_contractedRate (μ := sanovLaw) hSanov
    (fun ν => ∫ x, radialClamp R x ∂ν.toMeasure)
    (continuous_integral_radialClamp hR) (measurable_integral_radialClamp hR) hU
  rw [clampContractedRate_eq_of_pos μ₀ hR]
  have hev : ∀ᶠ n : ℕ in atTop,
      (sanovLaw n).map (fun ν => ∫ x, radialClamp R x ∂ν.toMeasure) =
        (Measure.pi fun _ : Fin n => μ₀).map (sampleClampMeanPi (d := d) (n := n) R) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    change
        (Measure.map
            (fun ω : Fin n → EuclideanSpace ℝ (Fin d) =>
              if hn' : 0 < n then empiricalProbabilityMeasure hn' ω
              else μ₀.toProbabilityMeasure)
            (Measure.pi fun _ : Fin n => μ₀)).map
          (fun ν => ∫ x, radialClamp R x ∂ν.toMeasure) =
        (Measure.pi fun _ : Fin n => μ₀).map (sampleClampMeanPi (d := d) (n := n) R)
    simp only [hn, ↓reduceDIte]
    exact map_sanovEmpirical_integral_radialClamp_eq_map_sampleClampMeanPi (μ := μ₀) hn hR
  have hfun :
      (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log
          (((sanovLaw n).map (fun ν => ∫ x, radialClamp R x ∂ν.toMeasure)) U)) =ᶠ[atTop]
        (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log
          ((Measure.pi fun _ : Fin n => μ₀).map
            (sampleClampMeanPi (d := d) (n := n) R) U)) := by
    filter_upwards [hev] with n hn; rw [hn]
  exact (le_of_eq (by rfl)).trans ((liminf_congr hfun ▸ hbound))

/-- Bound-only closed upper bound for clamp pushforwards at fixed `R > 0`. -/
theorem limsup_log_map_sampleClampMeanPi_le_iInf_clampContractedRate {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    {R : ℝ} (hR : 0 < R) {F : Set (EuclideanSpace ℝ (Fin d))} (hF : IsClosed F) :
    limsup (fun n => ((n : ℕ) : EReal)⁻¹ *
        ENNReal.log
          ((Measure.pi fun _ : Fin n => μ₀).map
            (sampleClampMeanPi (d := d) (n := n) R) F)) atTop ≤
      - (⨅ y ∈ F, (clampContractedRate μ₀ R y : EReal)) := by
  let sanovLaw : ℕ → Measure (ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) := fun n =>
    Measure.map
      (fun ω : Fin n → EuclideanSpace ℝ (Fin d) =>
        if hn : 0 < n then empiricalProbabilityMeasure hn ω
        else μ₀.toProbabilityMeasure)
      (Measure.pi fun _ : Fin n => μ₀)
  have hSanov :
      SatisfiesLDP sanovLaw
        (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
          klDiv (ν : Measure _) μ₀) :=
    satisfiesLDP_sanov_empiricalProbabilityMeasure (μ₀ := μ₀)
  have hbound := limsup_log_map_le_iInf_contractedRate (μ := sanovLaw) hSanov
    (fun ν => ∫ x, radialClamp R x ∂ν.toMeasure)
    (continuous_integral_radialClamp hR) (measurable_integral_radialClamp hR) hF
  rw [clampContractedRate_eq_of_pos μ₀ hR]
  have hev : ∀ᶠ n : ℕ in atTop,
      (sanovLaw n).map (fun ν => ∫ x, radialClamp R x ∂ν.toMeasure) =
        (Measure.pi fun _ : Fin n => μ₀).map (sampleClampMeanPi (d := d) (n := n) R) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    change
        (Measure.map
            (fun ω : Fin n → EuclideanSpace ℝ (Fin d) =>
              if hn' : 0 < n then empiricalProbabilityMeasure hn' ω
              else μ₀.toProbabilityMeasure)
            (Measure.pi fun _ : Fin n => μ₀)).map
          (fun ν => ∫ x, radialClamp R x ∂ν.toMeasure) =
        (Measure.pi fun _ : Fin n => μ₀).map (sampleClampMeanPi (d := d) (n := n) R)
    simp only [hn, ↓reduceDIte]
    exact map_sanovEmpirical_integral_radialClamp_eq_map_sampleClampMeanPi (μ := μ₀) hn hR
  have hfun :
      (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log
          (((sanovLaw n).map (fun ν => ∫ x, radialClamp R x ∂ν.toMeasure)) F)) =ᶠ[atTop]
        (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log
          ((Measure.pi fun _ : Fin n => μ₀).map
            (sampleClampMeanPi (d := d) (n := n) R) F)) := by
    filter_upwards [hev] with n hn; rw [hn]
  exact (limsup_congr hfun ▸ hbound).trans (le_of_eq (by rfl))

/-! ### Γ-rate identification (`clampContractedRate` ↔ `cramerRateFromSanov`) -/

/-- `liminf` along `ℝ` atTop is `≤` the discrete diagonal `n ↦ n+1`. -/
theorem liminf_atTop_le_liminf_nat_add_one (u : ℝ → ENNReal) :
    liminf u atTop ≤ liminf (fun n : ℕ => u ((n : ℝ) + 1)) atTop := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  -- `ht` is `map (n ↦ n+1) atTop ≤ atTop`, so liminf_ℝ ≤ liminf on the image filter
  have hle :
      liminf u atTop ≤
        liminf (u ∘ fun n : ℕ => (n : ℝ) + 1) atTop := by
    simpa [← Filter.liminf_comp] using
      (liminf_le_liminf_of_le (u := u) ht :
        liminf u atTop ≤
          liminf u ((atTop : Filter ℕ).map (fun n : ℕ => (n : ℝ) + 1)))
  convert hle using 2
  ext n; rfl

/-- Nearly-minimizer on a metric ball (ENNReal, additive slack). -/
theorem exists_mem_ball_le_ofReal_add
    {X : Type*} [PseudoMetricSpace X]
    (I : X → ENNReal) {y : X} {δ A ε : ℝ}
    (_hδ : 0 < δ) (_hA : 0 ≤ A) (hε : 0 < ε)
    (hinf : ⨅ z ∈ Metric.ball y δ, I z ≤ ENNReal.ofReal A) :
    ∃ z ∈ Metric.ball y δ, I z ≤ ENNReal.ofReal (A + ε) := by
  by_contra hnone
  push Not at hnone
  have hbig : ∀ z ∈ Metric.ball y δ, ENNReal.ofReal (A + ε) < I z := hnone
  have hle : ENNReal.ofReal (A + ε) ≤ ⨅ z ∈ Metric.ball y δ, I z :=
    le_iInf₂ fun z hz => (hbig z hz).le
  have hlt : ENNReal.ofReal A < ENNReal.ofReal (A + ε) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < A + ε)).2 (by linarith)
  exact (not_lt_of_ge (hle.trans hinf)) hlt

/-- Fiber recovery: `liminf_n inf_{ball} I_{n+1} ≤ kl` along a finite-KL fiber. -/
theorem liminf_iInf_ball_clampContractedRate_le_klDiv
    {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (hne : klDiv (ν : Measure _) μ₀ ≠ ∞)
    {δ : ℝ} (_hδ : 0 < δ) :
    liminf (fun n : ℕ =>
        ⨅ z ∈ Metric.ball (barycenter ν) δ,
          clampContractedRate μ₀ ((n : ℝ) + 1) z) atTop ≤
      klDiv (ν : Measure _) μ₀ := by
  have htend :=
    tendsto_integral_radialClamp_barycenter_of_klDiv_ne_top_of_HasFiniteMGF hMGF ν hne
  have hball : ∀ᶠ n : ℕ in atTop,
      ∫ x, radialClamp ((n : ℝ) + 1) x ∂ν.toMeasure ∈
        Metric.ball (barycenter ν) δ :=
    htend (Metric.ball_mem_nhds _ _hδ)
  have hrec : ∀ n : ℕ,
      clampContractedRate μ₀ ((n : ℝ) + 1)
          (∫ x, radialClamp ((n : ℝ) + 1) x ∂ν.toMeasure) ≤
        klDiv (ν : Measure _) μ₀ := by
    intro n
    simpa [clampContractedRate_eq_of_pos μ₀ (Nat.cast_add_one_pos n)] using
      contractedRate_integral_radialClamp_recovery_le_klDiv_of_HasFiniteMGF
        hMGF ν hne n
  have hle : ∀ᶠ n : ℕ in atTop,
      (⨅ z ∈ Metric.ball (barycenter ν) δ,
          clampContractedRate μ₀ ((n : ℝ) + 1) z) ≤
        klDiv (ν : Measure _) μ₀ := by
    filter_upwards [hball] with n hn
    exact (iInf₂_le _ hn).trans (hrec n)
  exact (liminf_le_limsup).trans (limsup_le_of_le (by isBoundedDefault) hle)

theorem gammaLiminfRate_clampContractedRate_le_klDiv_of_barycenter
    {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (hne : klDiv (ν : Measure _) μ₀ ≠ ∞) :
    gammaLiminfRate (clampContractedRate μ₀) (barycenter ν) ≤
      klDiv (ν : Measure _) μ₀ := by
  refine iSup_le fun δ => ?_
  have hnat := liminf_iInf_ball_clampContractedRate_le_klDiv hMGF ν hne δ.2
  have hreal := liminf_atTop_le_liminf_nat_add_one
    (fun R => ⨅ z ∈ Metric.ball (barycenter ν) δ.1, clampContractedRate μ₀ R z)
  exact hreal.trans hnat


/-- (2) Recovery: `gammaLiminfRate clampContractedRate ≤ cramerRateFromSanov`. -/
theorem gammaLiminfRate_clampContractedRate_le_cramerRateFromSanov
    {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (y : EuclideanSpace ℝ (Fin d)) :
    gammaLiminfRate (clampContractedRate μ₀) y ≤ cramerRateFromSanov μ₀ y := by
  unfold cramerRateFromSanov contractedRate
  refine le_iInf₂ fun ν hν => ?_
  have hy : barycenter ν = y := by
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using hν
  by_cases hne : klDiv (ν : Measure _) μ₀ = ∞
  · simp [hne]
  · simpa [hy] using
      gammaLiminfRate_clampContractedRate_le_klDiv_of_barycenter hMGF ν hne

/-! ### (1) Pointwise real-parameter Γ-liminf toward Sanov/CRF -/

/-- `radialClamp R x → x` as `R → ∞` along `ℝ`. -/
theorem tendsto_radialClamp_atTop {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) : Tendsto (fun R : ℝ => radialClamp R x) atTop (𝓝 x) := by
  refine tendsto_atTop_of_eventually_const (i₀ := ‖x‖) fun R hR => ?_
  have hR0 : 0 ≤ R := (norm_nonneg x).trans hR
  exact radialClamp_of_norm_le hR0 hR

/-- Clamp-MGF → MGF along real `R → ∞` under `HasFiniteMGF`. -/
theorem tendsto_integral_exp_inner_radialClamp_atTop_of_HasFiniteMGF {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀) (t : EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun R : ℝ => ∫ x, Real.exp (⟪t, radialClamp R x⟫_ℝ) ∂μ₀) atTop
      (𝓝 (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀)) := by
  have hexp_id : Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (‖t‖ * ‖x‖)) μ₀ :=
    hMGF.integrable_exp_mul_norm ‖t‖
  have hlim :=
    tendsto_integral_filter_of_dominated_convergence
      (α := EuclideanSpace ℝ (Fin d)) (G := ℝ) (μ := μ₀)
      (l := (atTop : Filter ℝ))
      (F := fun (R : ℝ) x => Real.exp (⟪t, radialClamp R x⟫_ℝ))
      (f := fun x => Real.exp (⟪t, x⟫_ℝ))
      (bound := fun x => Real.exp (‖t‖ * ‖x‖))
      ?meas ?bound hexp_id ?pt
  · exact hlim
  case meas =>
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact (Real.continuous_exp.comp (continuous_inner_radialClamp t hR)).aestronglyMeasurable
  case bound =>
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
        exp_inner_radialClamp_le_exp_mul_norm t hR x
  case pt =>
    exact Eventually.of_forall fun x =>
      (Real.continuous_exp.tendsto _).comp
        (((innerSL ℝ t).continuous.tendsto _).comp (tendsto_radialClamp_atTop x))

theorem tendsto_log_integral_exp_inner_radialClamp_atTop_of_HasFiniteMGF {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀) (t : EuclideanSpace ℝ (Fin d)) :
    Tendsto
      (fun R : ℝ => Real.log (∫ x, Real.exp (⟪t, radialClamp R x⟫_ℝ) ∂μ₀)) atTop
      (𝓝 (Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀))) := by
  have hpos : 0 < ∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀ := integral_exp_pos (hMGF t)
  exact (Real.continuousAt_log hpos.ne').tendsto.comp
    (tendsto_integral_exp_inner_radialClamp_atTop_of_HasFiniteMGF hMGF t)

/-- Pointwise Fenchel–Young competitor ≤ liminf_R clamp-contracted rate. -/
theorem liminf_clampContractedRate_ge_ofReal_fy_of_HasFiniteMGF {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (y t : EuclideanSpace ℝ (Fin d)) :
    ENNReal.ofReal
        (⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t) ≤
      liminf (fun R : ℝ => clampContractedRate μ₀ R y) atTop := by
  have hfy :
      Tendsto
        (fun R : ℝ =>
          ⟪t, y⟫_ℝ - Real.log (∫ x, Real.exp (⟪t, radialClamp R x⟫_ℝ) ∂μ₀)) atTop
        (𝓝 (⟪t, y⟫_ℝ - Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀))) :=
    tendsto_const_nhds.sub
      (tendsto_log_integral_exp_inner_radialClamp_atTop_of_HasFiniteMGF hMGF t)
  have hofReal :
      Tendsto
        (fun R : ℝ =>
          ENNReal.ofReal
            (⟪t, y⟫_ℝ - Real.log (∫ x, Real.exp (⟪t, radialClamp R x⟫_ℝ) ∂μ₀))) atTop
        (𝓝
          (ENNReal.ofReal
            (⟪t, y⟫_ℝ - Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀)))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp hfy
  have hle : ∀ᶠ R : ℝ in atTop,
      ENNReal.ofReal
          (⟪t, y⟫_ℝ - Real.log (∫ x, Real.exp (⟪t, radialClamp R x⟫_ℝ) ∂μ₀)) ≤
        clampContractedRate μ₀ R y := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    simpa [clampContractedRate_eq_of_pos μ₀ hR] using
      ofReal_inner_sub_log_clampMGF_le_contractedRate_integral_radialClamp μ₀ y t hR
  have hliminf := liminf_le_liminf hle
  have hlogid :
      ⟪t, y⟫_ℝ - Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀) =
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t := by
    simp [logMGFVec_id]
  simpa [hofReal.liminf_eq, hlogid] using hliminf

theorem liminf_clampContractedRate_ge_cramerRateFunction_of_HasFiniteMGF {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (y : EuclideanSpace ℝ (Fin d))
    (hbdd : BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
      ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t)) :
    cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y ≤
      liminf (fun R : ℝ => clampContractedRate μ₀ R y) atTop := by
  refine cramerRateFunction_le_of_forall_ofReal_inner_sub_logMGF_le
    (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y _ hbdd fun t => ?_
  exact liminf_clampContractedRate_ge_ofReal_fy_of_HasFiniteMGF hMGF y t

/-- Pointwise: Sanov rate ≤ liminf_R clamp-contracted rate (via rate ID). -/
theorem liminf_clampContractedRate_ge_cramerRateFromSanov_of_HasFiniteMGF_of_forall_bddAbove
    {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t))
    (y : EuclideanSpace ℝ (Fin d)) :
    cramerRateFromSanov μ₀ y ≤
      liminf (fun R : ℝ => clampContractedRate μ₀ R y) atTop := by
  have heq := cramerRateFromSanov_eq_cramerRateFunction_of_tiltCover_no_hid
    μ₀ hMGF (TiltCover_of_HasFiniteMGF_of_forall_bddAbove μ₀ hMGF hbdd) hbdd y
  rw [heq]
  exact liminf_clampContractedRate_ge_cramerRateFunction_of_HasFiniteMGF
    hMGF y (hbdd y)

/-- Real-parameter Γ-liminf along every `R_n → ∞` diagonal. -/
theorem GammaLiminfReal_clampContractedRate_cramerRateFromSanov
    {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t)) :
    GammaLiminfReal (clampContractedRate μ₀) (cramerRateFromSanov μ₀) := by
  intro y R hR yseq hy
  have heq := cramerRateFromSanov_eq_cramerRateFunction_of_tiltCover_no_hid
    μ₀ hMGF (TiltCover_of_HasFiniteMGF_of_forall_bddAbove μ₀ hMGF hbdd) hbdd y
  rw [heq]
  refine cramerRateFunction_le_of_forall_ofReal_inner_sub_logMGF_le
    (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y _ (hbdd y) fun t => ?_
  have hRpos : ∀ᶠ n : ℕ in atTop, 0 < R n :=
    hR.eventually (eventually_gt_atTop (0 : ℝ))
  have hfy :
      Tendsto
        (fun n : ℕ =>
          ⟪t, yseq n⟫_ℝ - Real.log (∫ x, Real.exp (⟪t, radialClamp (R n) x⟫_ℝ) ∂μ₀)) atTop
        (𝓝 (⟪t, y⟫_ℝ - Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀))) := by
    have hinner : Tendsto (fun n : ℕ => ⟪t, yseq n⟫_ℝ) atTop (𝓝 ⟪t, y⟫_ℝ) :=
      ((innerSL ℝ t).continuous.tendsto y).comp hy
    have hlog :=
      (tendsto_log_integral_exp_inner_radialClamp_atTop_of_HasFiniteMGF hMGF t).comp hR
    exact hinner.sub hlog
  have hofReal :
      Tendsto
        (fun n : ℕ =>
          ENNReal.ofReal
            (⟪t, yseq n⟫_ℝ -
              Real.log (∫ x, Real.exp (⟪t, radialClamp (R n) x⟫_ℝ) ∂μ₀))) atTop
        (𝓝
          (ENNReal.ofReal
            (⟪t, y⟫_ℝ - Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀)))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp hfy
  have hle : ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal
          (⟪t, yseq n⟫_ℝ -
            Real.log (∫ x, Real.exp (⟪t, radialClamp (R n) x⟫_ℝ) ∂μ₀)) ≤
        clampContractedRate μ₀ (R n) (yseq n) := by
    filter_upwards [hRpos] with n hRn
    simpa [clampContractedRate_eq_of_pos μ₀ hRn] using
      ofReal_inner_sub_log_clampMGF_le_contractedRate_integral_radialClamp
        μ₀ (yseq n) t hRn
  have hliminf := liminf_le_liminf hle
  have hlogid :
      ⟪t, y⟫_ℝ - Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀) =
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t := by
    simp [logMGFVec_id]
  simpa [hofReal.liminf_eq, hlogid] using hliminf

/-! ### (1) `cramerRateFromSanov ≤ gammaLiminfRate` via nearly-mins + compactness -/

/-- Nearly-minimizer on a ball when the ball-inf is finite. -/
theorem exists_mem_ball_le_iInf_add
    {X : Type*} [PseudoMetricSpace X]
    (I : X → ENNReal) {y : X} {δ : ℝ} (_hδ : 0 < δ) {ε : ENNReal}
    (hε : ε ≠ 0) (hfin : (⨅ z ∈ Metric.ball y δ, I z) ≠ ∞) :
    ∃ z ∈ Metric.ball y δ, I z ≤ (⨅ w ∈ Metric.ball y δ, I w) + ε := by
  let a := ⨅ z ∈ Metric.ball y δ, I z
  have hlt : a < a + ε := ENNReal.lt_add_right hfin hε
  have ha : a = ⨅ z : Metric.ball y δ, I (z : X) := by simp [a, iInf_subtype]
  have hsub : (⨅ z : Metric.ball y δ, I (z : X)) <
      (⨅ z : Metric.ball y δ, I (z : X)) + ε := by
    simpa [← ha] using hlt
  obtain ⟨⟨z, hz⟩, hzlt⟩ := iInf_lt_iff.mp hsub
  exact ⟨z, hz, hzlt.le.trans_eq (congrArg (· + ε) ha.symm)⟩

/-- Nhds liminf equals the ball expression used by `gammaLiminfRate`. -/
theorem liminf_nhds_eq_iSup_iInf_ball {X : Type*} [PseudoMetricSpace X]
    (f : X → ENNReal) (x : X) :
    liminf f (𝓝 x) =
      ⨆ δ : {δ : ℝ // 0 < δ}, ⨅ y ∈ Metric.ball x δ.1, f y := by
  have hbas : (𝓝 x).HasBasis (fun δ : ℝ => 0 < δ) (fun δ => Metric.ball x δ) :=
    Metric.nhds_basis_ball
  rw [hbas.liminf_eq_iSup_iInf]
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun δ hδ =>
      le_iSup (fun d : {δ : ℝ // 0 < δ} => ⨅ y ∈ Metric.ball x d.1, f y) ⟨δ, hδ⟩
  · refine iSup_le fun δ => ?_
    refine (le_iSup (fun _ : 0 < δ.1 => ⨅ y ∈ Metric.ball x δ.1, f y) δ.2).trans ?_
    exact le_iSup (fun δ' => ⨆ (_ : 0 < δ'), ⨅ y ∈ Metric.ball x δ', f y) δ.1

/-- Compact Γ-extraction: closed-ball inf of `J` ≤ liminf of open-ball infs of `I_R`. -/
theorem iInf_closedBall_le_liminf_iInf_ball_of_GammaLiminfReal
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    (I : ℝ → X → ENNReal) (J : X → ENNReal)
    (hΓ : GammaLiminfReal I J)
    (y : X) {δ : ℝ} (hδ : 0 < δ) :
    (⨅ z ∈ Metric.closedBall y δ, J z) ≤
      liminf (fun R : ℝ => ⨅ z ∈ Metric.ball y δ, I R z) atTop := by
  set c := ⨅ z ∈ Metric.closedBall y δ, J z
  set v : ℝ → ENNReal := fun R => ⨅ z ∈ Metric.ball y δ, I R z
  rw [le_liminf_iff (u := v)]
  intro b hb
  by_contra hnot
  have hfreq : ∃ᶠ R : ℝ in atTop, v R ≤ b := by
    have : ∃ᶠ R : ℝ in atTop, ¬b < v R := not_eventually.mp hnot
    exact this.mono fun _ h => le_of_not_gt h
  have hpick : ∀ n : ℕ, ∃ R : ℝ, (n : ℝ) + 1 ≤ R ∧ v R ≤ b := by
    intro n
    obtain ⟨R, hRge, hRv⟩ := Frequently.forall_exists_of_atTop hfreq ((n : ℝ) + 1)
    exact ⟨R, hRge, hRv⟩
  choose R hRge hRv using hpick
  have hRtend : Tendsto R atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro t
    refine ⟨Nat.ceil t, fun n hn => ?_⟩
    have hceil : (Nat.ceil t : ℝ) ≤ n := by exact_mod_cast hn
    have hnR : (n : ℝ) + 1 ≤ R n := hRge n
    have ht : t ≤ (Nat.ceil t : ℝ) := Nat.le_ceil t
    linarith
  have hz : ∀ n : ℕ,
      ∃ z ∈ Metric.ball y δ,
        I (R n) z ≤ v (R n) + ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
    intro n
    by_cases hfin : v (R n) = ∞
    · refine ⟨y, Metric.mem_ball_self hδ, ?_⟩
      simp [hfin]
    · have hε : ENNReal.ofReal (1 / (n + 1 : ℝ)) ≠ 0 :=
        (ENNReal.ofReal_pos.2 (by positivity)).ne'
      exact exists_mem_ball_le_iInf_add (I (R n)) hδ hε hfin
  choose z hzball hznear using hz
  have hzclosed : ∀ n, z n ∈ Metric.closedBall y δ :=
    fun n => Metric.ball_subset_closedBall (hzball n)
  have hK : IsCompact (Metric.closedBall y δ) := isCompact_closedBall y δ
  obtain ⟨zstar, hzstar, φ, hφmono, hφtend⟩ := hK.tendsto_subseq hzclosed
  have hRφ : Tendsto (R ∘ φ) atTop atTop := hRtend.comp hφmono.tendsto_atTop
  have hΓz : J zstar ≤ liminf (fun k => I (R (φ k)) (z (φ k))) atTop :=
    hΓ zstar (R ∘ φ) hRφ (z ∘ φ) hφtend
  have hlimI :
      liminf (fun k => I (R (φ k)) (z (φ k))) atTop ≤
        liminf (fun k => v (R (φ k)) + ENNReal.ofReal (1 / (φ k + 1 : ℝ))) atTop :=
    liminf_le_liminf (Eventually.of_forall fun k => hznear (φ k))
  have hlimv :
      liminf (fun k => v (R (φ k)) + ENNReal.ofReal (1 / (φ k + 1 : ℝ))) atTop ≤ b := by
    have hle :
        ∀ᶠ k : ℕ in atTop,
          v (R (φ k)) + ENNReal.ofReal (1 / (φ k + 1 : ℝ)) ≤
            b + ENNReal.ofReal (1 / (φ k + 1 : ℝ)) :=
      Eventually.of_forall fun k =>
        add_le_add (hRv (φ k)) le_rfl
    refine (liminf_le_liminf hle).trans ?_
    have hslack :
        Tendsto (fun k : ℕ => ENNReal.ofReal (1 / (φ k + 1 : ℝ))) atTop (𝓝 0) := by
      have hbase :=
        ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
      change Tendsto ((fun a : ℕ => ENNReal.ofReal (1 / (a + 1 : ℝ))) ∘ φ) atTop (𝓝 0)
      simpa [ENNReal.ofReal_zero] using hbase.comp hφmono.tendsto_atTop
    have heq := (tendsto_const_nhds (x := b).add hslack).liminf_eq
    simpa using heq.le
  have hzle : J zstar ≤ b := hΓz.trans (hlimI.trans hlimv)
  have hc : c ≤ J zstar := iInf₂_le zstar hzstar
  exact (not_lt_of_ge (hc.trans hzle)) hb

/-- LSC + GammaLiminfReal + properness ⇒ `J ≤ gammaLiminfRate I`. -/
theorem le_gammaLiminfRate_of_GammaLiminfReal_of_lowerSemicontinuous
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    (I : ℝ → X → ENNReal) (J : X → ENNReal)
    (hΓ : GammaLiminfReal I J)
    (hLSC : LowerSemicontinuous J)
    (y : X) :
    J y ≤ gammaLiminfRate I y := by
  have hnhds : J y ≤ liminf J (𝓝 y) := hLSC.le_liminf y
  rw [liminf_nhds_eq_iSup_iInf_ball] at hnhds
  refine hnhds.trans (iSup_le fun δ => ?_)
  -- For each δ: inf_ball(δ) J ≤ inf_closedBall(δ/2) J ≤ liminf inf_ball(δ/2) I ≤ gamma
  have hδ2 : 0 < δ.1 / 2 := half_pos δ.2
  have hsub : Metric.closedBall y (δ.1 / 2) ⊆ Metric.ball y δ.1 := by
    intro z hz
    exact (Metric.mem_closedBall.mp hz).trans_lt (half_lt_self δ.2)
  calc
    (⨅ z ∈ Metric.ball y δ.1, J z) ≤
        ⨅ z ∈ Metric.closedBall y (δ.1 / 2), J z :=
      iInf_le_iInf_of_subset hsub
    _ ≤ liminf (fun R => ⨅ z ∈ Metric.ball y (δ.1 / 2), I R z) atTop :=
      iInf_closedBall_le_liminf_iInf_ball_of_GammaLiminfReal I J hΓ y hδ2
    _ ≤ gammaLiminfRate I y :=
      le_iSup (fun d : {δ : ℝ // 0 < δ} =>
          liminf (fun R => ⨅ z ∈ Metric.ball y d.1, I R z) atTop)
        ⟨δ.1 / 2, hδ2⟩

/-- (1) Sanov ≤ Γ-rate under `HasFiniteMGF` + `forall_bddAbove`. -/
theorem cramerRateFromSanov_le_gammaLiminfRate_clampContractedRate
    {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t))
    (y : EuclideanSpace ℝ (Fin d)) :
    cramerRateFromSanov μ₀ y ≤
      gammaLiminfRate (clampContractedRate μ₀) y := by
  have hΓ := GammaLiminfReal_clampContractedRate_cramerRateFromSanov hMGF hbdd
  have heq := cramerRateFromSanov_eq_cramerRateFunction_of_tiltCover_no_hid
    μ₀ hMGF (TiltCover_of_HasFiniteMGF_of_forall_bddAbove μ₀ hMGF hbdd) hbdd
  have hLSC : LowerSemicontinuous (cramerRateFromSanov μ₀) :=
    (funext heq) ▸ lowerSemicontinuous_cramerRateFunction_of_HasFiniteMGF μ₀ hMGF hbdd
  exact le_gammaLiminfRate_of_GammaLiminfReal_of_lowerSemicontinuous
    (clampContractedRate μ₀) (cramerRateFromSanov μ₀) hΓ hLSC y

/-- Identification both ways. -/
theorem gammaLiminfRate_clampContractedRate_eq_cramerRateFromSanov
    {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t))
    (y : EuclideanSpace ℝ (Fin d)) :
    gammaLiminfRate (clampContractedRate μ₀) y =
      cramerRateFromSanov μ₀ y :=
  le_antisymm
    (gammaLiminfRate_clampContractedRate_le_cramerRateFromSanov hMGF y)
    (cramerRateFromSanov_le_gammaLiminfRate_clampContractedRate hMGF hbdd y)



/-! ### (3)+(4)+(5): hClosed, good Γ-rate, wire DZ 4.2.16 → drop `hLDP` -/

/-- `R`-free dominate of the clamp dual integrand. -/
theorem log_integral_exp_inner_radialClamp_le_log_exp_mul_norm_of_HasFiniteMGF
    {d : ℕ} {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀) (t : EuclideanSpace ℝ (Fin d)) {R : ℝ} (hR : 0 < R) :
    Real.log (∫ x, Real.exp (⟪t, radialClamp R x⟫_ℝ) ∂μ₀) ≤
      Real.log (∫ x, Real.exp (‖t‖ * ‖x‖) ∂μ₀) := by
  have hexp_dom : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      Real.exp (‖t‖ * ‖x‖)) μ₀ :=
    hMGF.integrable_exp_mul_norm ‖t‖
  have hpoint : ∀ x, Real.exp (⟪t, radialClamp R x⟫_ℝ) ≤ Real.exp (‖t‖ * ‖x‖) := by
    intro x
    refine Real.exp_le_exp.mpr ?_
    exact (real_inner_le_norm t (radialClamp R x)).trans
      (mul_le_mul_of_nonneg_left (norm_radialClamp_le_norm hR.le x) (norm_nonneg _))
  have hexp_clamp : Integrable (fun x => Real.exp (⟪t, radialClamp R x⟫_ℝ)) μ₀ :=
    Integrable.mono' hexp_dom
      (Real.continuous_exp.comp ((innerSL ℝ t).continuous.comp
        (continuous_radialClamp hR))).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hpoint x)
  have hInt :
      (∫ x, Real.exp (⟪t, radialClamp R x⟫_ℝ) ∂μ₀) ≤
        ∫ x, Real.exp (‖t‖ * ‖x‖) ∂μ₀ :=
    integral_mono hexp_clamp hexp_dom hpoint
  have hpos_clamp : 0 < ∫ x, Real.exp (⟪t, radialClamp R x⟫_ℝ) ∂μ₀ :=
    integral_exp_pos hexp_clamp
  exact (Real.log_le_log_iff hpos_clamp (lt_of_lt_of_le hpos_clamp hInt)).mpr hInt

/-- Coercivity: clamp-contracted finite sublevel points are norm-bounded, uniformly in `R ≥ 1`. -/
theorem exists_norm_le_of_clampContractedRate_le_ofReal_of_HasFiniteMGF
    {d : ℕ} {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀) (a : ℝ) :
    ∃ M : ℝ, ∀ (y : EuclideanSpace ℝ (Fin d)) (R : ℝ),
      1 ≤ R → clampContractedRate μ₀ R y ≤ ENNReal.ofReal a → ‖y‖ ≤ M := by
  have hcont := continuous_logMGFVec_id_of_HasFiniteMGF μ₀ hMGF
  rcases (Metric.continuousAt_iff.mp (hcont.continuousAt (x := 0))) (1 : ℝ) (by norm_num) with
    ⟨δ, hδpos, _hδ⟩
  have hδ2 : 0 < δ / 2 := half_pos hδpos
  have hdom : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      Real.exp ((δ / 2) * ‖x‖)) μ₀ :=
    hMGF.integrable_exp_mul_norm (δ / 2)
  have hpos_dom : 0 < ∫ x, Real.exp ((δ / 2) * ‖x‖) ∂μ₀ := integral_exp_pos hdom
  set C : ℝ := Real.log (∫ x, Real.exp ((δ / 2) * ‖x‖) ∂μ₀)
  have hC0 : 0 ≤ C := by
    have hInt1 : (1 : ℝ) ≤ ∫ x, Real.exp ((δ / 2) * ‖x‖) ∂μ₀ := by
      have hpt : ∀ x : EuclideanSpace ℝ (Fin d),
          (1 : ℝ) ≤ Real.exp ((δ / 2) * ‖x‖) := fun x =>
        Real.one_le_exp (mul_nonneg hδ2.le (norm_nonneg x))
      simpa [integral_const, measure_univ] using
        integral_mono (integrable_const (1 : ℝ)) hdom hpt
    exact Real.log_nonneg hInt1
  refine ⟨(max a 0 + C + 1) / (δ / 2) + 1, ?_⟩
  intro y R hRge hyrate
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hRge
  by_cases hy0 : y = 0
  · subst hy0
    simpa [norm_zero] using
      (add_nonneg (div_nonneg (add_nonneg (add_nonneg (le_max_right a 0) hC0)
        zero_le_one) hδ2.le) zero_le_one)
  · have hx0 : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    let t : EuclideanSpace ℝ (Fin d) := ((δ / 2) / ‖y‖) • y
    have htnorm : ‖t‖ = δ / 2 := by
      change ‖((δ / 2) / ‖y‖) • y‖ = δ / 2
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hδ2 hx0),
        div_mul_cancel₀ _ hx0.ne']
    have hinner : ⟪t, y⟫_ℝ = (δ / 2) * ‖y‖ := by
      change ⟪((δ / 2) / ‖y‖) • y, y⟫_ℝ = (δ / 2) * ‖y‖
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp [hx0.ne']
    have hlog_le :
        Real.log (∫ x, Real.exp (⟪t, radialClamp R x⟫_ℝ) ∂μ₀) ≤ C := by
      simpa [C, htnorm] using
        log_integral_exp_inner_radialClamp_le_log_exp_mul_norm_of_HasFiniteMGF hMGF t hR
    have hcomp :
        ENNReal.ofReal (⟪t, y⟫_ℝ -
            Real.log (∫ x, Real.exp (⟪t, radialClamp R x⟫_ℝ) ∂μ₀)) ≤
          ENNReal.ofReal a := by
      refine (le_trans ?_ hyrate)
      simpa [clampContractedRate_eq_of_pos μ₀ hR] using
        ofReal_inner_sub_log_clampMGF_le_contractedRate_integral_radialClamp μ₀ y t hR
    have harg :
        ⟪t, y⟫_ℝ - Real.log (∫ x, Real.exp (⟪t, radialClamp R x⟫_ℝ) ∂μ₀) ≤
          max a 0 := by
      have hle' :
          ENNReal.ofReal (⟪t, y⟫_ℝ -
              Real.log (∫ x, Real.exp (⟪t, radialClamp R x⟫_ℝ) ∂μ₀)) ≤
            ENNReal.ofReal (max a 0) :=
        hcomp.trans (ENNReal.ofReal_le_ofReal (le_max_left a 0))
      exact (ENNReal.ofReal_le_ofReal_iff (le_max_right a 0)).mp hle'
    have hlin : (δ / 2) * ‖y‖ - C ≤ max a 0 := by
      have : (δ / 2) * ‖y‖ -
          Real.log (∫ x, Real.exp (⟪t, radialClamp R x⟫_ℝ) ∂μ₀) ≤ max a 0 := by
        simpa [hinner] using harg
      linarith [hlog_le]
    have hdiv : ‖y‖ ≤ (max a 0 + C) / (δ / 2) :=
      (le_div_iff₀ hδ2).mpr (by linarith)
    have hstep : (max a 0 + C) / (δ / 2) ≤ (max a 0 + C + 1) / (δ / 2) + 1 := by
      have : (max a 0 + C) / (δ / 2) ≤ (max a 0 + C + 1) / (δ / 2) :=
        div_le_div_of_nonneg_right (by linarith) hδ2.le
      exact this.trans (le_of_lt (lt_add_one _))
    exact hdiv.trans hstep

/-- Nearly-minimizer on an arbitrary set with finite inf. -/
theorem exists_mem_le_iInf_add {X : Type*}
    (I : X → ENNReal) {G : Set X} {ε : ENNReal}
    (hε : ε ≠ 0) (hfin : (⨅ z ∈ G, I z) ≠ ∞) :
    ∃ z ∈ G, I z ≤ (⨅ w ∈ G, I w) + ε := by
  classical
  let a := ⨅ z ∈ G, I z
  have hlt : a < a + ε := ENNReal.lt_add_right hfin hε
  have ha : a = ⨅ z : G, I (z : X) := by simp [a, iInf_subtype]
  have hsub : (⨅ z : G, I (z : X)) < (⨅ z : G, I (z : X)) + ε := by
    simpa [← ha] using hlt
  obtain ⟨⟨z, hz⟩, hzlt⟩ := iInf_lt_iff.mp hsub
  exact ⟨z, hz, hzlt.le.trans_eq (congrArg (· + ε) ha.symm)⟩


/-- Closed-set Γ-liminf inequality (ENNReal) for clamp ↔ Sanov. -/
theorem iInf_cramerRateFromSanov_le_liminf_iInf_clampContractedRate
    {d : ℕ} {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t))
    {G : Set (EuclideanSpace ℝ (Fin d))} (hG : IsClosed G) :
    (⨅ y ∈ G, cramerRateFromSanov μ₀ y) ≤
      liminf (fun R : ℝ => ⨅ y ∈ G, clampContractedRate μ₀ R y) atTop := by
  set J := cramerRateFromSanov μ₀
  set v : ℝ → ENNReal := fun R => ⨅ y ∈ G, clampContractedRate μ₀ R y
  have hΓ := GammaLiminfReal_clampContractedRate_cramerRateFromSanov hMGF hbdd
  rw [le_liminf_iff (u := v)]
  intro b hb
  by_contra hnot
  have hfreq : ∃ᶠ R : ℝ in atTop, v R ≤ b :=
    (not_eventually.mp hnot).mono fun _ h => le_of_not_gt h
  have hpick : ∀ n : ℕ, ∃ R : ℝ, (n : ℝ) + 1 ≤ R ∧ v R ≤ b := by
    intro n
    obtain ⟨R, hRge, hRv⟩ := Frequently.forall_exists_of_atTop hfreq ((n : ℝ) + 1)
    exact ⟨R, hRge, hRv⟩
  choose R hRge hRv using hpick
  have hRtend : Tendsto R atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro t
    refine ⟨Nat.ceil t, fun n hn => ?_⟩
    have : (n : ℝ) + 1 ≤ R n := hRge n
    have : (Nat.ceil t : ℝ) ≤ n := by exact_mod_cast hn
    have : t ≤ (Nat.ceil t : ℝ) := Nat.le_ceil t
    linarith
  have hbne : b ≠ ∞ := ne_top_of_lt hb
  set a : ℝ := b.toReal
  have hbEq : b = ENNReal.ofReal a := (ENNReal.ofReal_toReal hbne).symm
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  obtain ⟨M, hMbound⟩ :=
    exists_norm_le_of_clampContractedRate_le_ofReal_of_HasFiniteMGF hMGF (a + 1)
  have hz : ∀ n : ℕ,
      ∃ z ∈ G, clampContractedRate μ₀ (R n) z ≤
        v (R n) + ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
    intro n
    by_cases hfin : v (R n) = ∞
    · have : ¬ v (R n) ≤ b := by
        rw [hfin, hbEq]
        exact not_le_of_gt ENNReal.ofReal_lt_top
      exact absurd (hRv n) this
    · exact exists_mem_le_iInf_add (clampContractedRate μ₀ (R n))
        ((ENNReal.ofReal_pos.2 (by positivity)).ne') hfin
  choose z hzG hznear using hz
  let z' : ℕ → EuclideanSpace ℝ (Fin d) := fun k => z (k + 1)
  have hz'In : ∀ k,
      z' k ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) M ∩ G := by
    intro k
    have hR1 : 1 ≤ R (k + 1) := by
      have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) + 1 := by
        exact_mod_cast (Nat.le_add_left 1 (k + 1))
      exact this.trans (hRge (k + 1))
    have hεle : ENNReal.ofReal (1 / ((k + 1 : ℕ) + 1 : ℝ)) ≤ ENNReal.ofReal 1 :=
      ENNReal.ofReal_le_ofReal (by
        have hpos : (0 : ℝ) < (k + 1 : ℕ) + 1 := by positivity
        exact (div_le_one hpos).mpr (by exact_mod_cast Nat.le_add_left 1 (k + 1)))
    have hsum : v (R (k + 1)) + ENNReal.ofReal (1 / ((k + 1 : ℕ) + 1 : ℝ)) ≤
        ENNReal.ofReal a + ENNReal.ofReal 1 :=
      add_le_add (by simpa [hbEq] using hRv (k + 1)) hεle
    have hadd : ENNReal.ofReal a + ENNReal.ofReal 1 = ENNReal.ofReal (a + 1) :=
      (ENNReal.ofReal_add ha0 zero_le_one).symm
    have hyrate : clampContractedRate μ₀ (R (k + 1)) (z' k) ≤ ENNReal.ofReal (a + 1) :=
      (hznear (k + 1)).trans (hsum.trans_eq hadd)
    refine ⟨?_, hzG (k + 1)⟩
    exact Metric.mem_closedBall.mpr (by
      simpa [dist_eq_norm, z'] using hMbound (z (k + 1)) (R (k + 1)) hR1 hyrate)
  have hK : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) M ∩ G) :=
    (isCompact_closedBall _ _).inter_right hG
  obtain ⟨zstar, hzstar, φ, hφmono, hφtend⟩ := hK.tendsto_subseq hz'In
  have hzstarG : zstar ∈ G := hzstar.2
  have hφ1 : Tendsto (fun k => φ k + 1) atTop atTop := by
    have hφtop := hφmono.tendsto_atTop
    rw [tendsto_atTop_atTop] at hφtop ⊢
    intro n
    obtain ⟨N, hN⟩ := hφtop n
    exact ⟨N, fun k hk => (hN k hk).trans (Nat.le_add_right _ 1)⟩
  have hRφ : Tendsto (fun k => R (φ k + 1)) atTop atTop :=
    hRtend.comp hφ1
  have hΓz : J zstar ≤
      liminf (fun k => clampContractedRate μ₀ (R (φ k + 1)) (z (φ k + 1))) atTop :=
    hΓ zstar (fun k => R (φ k + 1)) hRφ (fun k => z (φ k + 1)) hφtend
  have hlimI :
      liminf (fun k => clampContractedRate μ₀ (R (φ k + 1)) (z (φ k + 1))) atTop ≤
        liminf (fun k => v (R (φ k + 1)) +
          ENNReal.ofReal (1 / ((φ k + 1 : ℕ) + 1 : ℝ))) atTop :=
    liminf_le_liminf (Eventually.of_forall fun k => hznear (φ k + 1))
  have hlimv :
      liminf (fun k => v (R (φ k + 1)) +
          ENNReal.ofReal (1 / ((φ k + 1 : ℕ) + 1 : ℝ))) atTop ≤ b := by
    have hle :
        ∀ᶠ k : ℕ in atTop,
          v (R (φ k + 1)) + ENNReal.ofReal (1 / ((φ k + 1 : ℕ) + 1 : ℝ)) ≤
            b + ENNReal.ofReal (1 / ((φ k + 1 : ℕ) + 1 : ℝ)) :=
      Eventually.of_forall fun k => add_le_add (hRv (φ k + 1)) le_rfl
    refine (liminf_le_liminf hle).trans ?_
    have hslack :
        Tendsto (fun k : ℕ =>
          ENNReal.ofReal (1 / ((φ k + 1 : ℕ) + 1 : ℝ))) atTop (𝓝 0) := by
      have hbase := ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
      have hmono : StrictMono (fun k : ℕ => φ k + 1) :=
        fun _ _ h => Nat.add_lt_add_right (hφmono h) 1
      change Tendsto
        ((fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ))) ∘ fun k => φ k + 1)
        atTop (𝓝 0)
      simpa [ENNReal.ofReal_zero] using hbase.comp hmono.tendsto_atTop
    have heq := (tendsto_const_nhds (x := b).add hslack).liminf_eq
    simpa using heq.le
  have hzle : J zstar ≤ b := hΓz.trans (hlimI.trans hlimv)
  have hc : (⨅ y ∈ G, J y) ≤ J zstar := iInf₂_le zstar hzstarG
  exact (not_lt_of_ge (hc.trans hzle)) hb


/-- (3) Closed-set `hClosed` for the Γ-rate.
Uses ENNReal closed-set liminf + `EReal.liminf_coe_ennreal_eq` + `liminf_le_limsup`. -/
theorem hClosed_gammaLiminfRate_clampContractedRate
    {d : ℕ} {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t))
    (G : Set (EuclideanSpace ℝ (Fin d))) (hG : IsClosed G) :
    (⨅ x ∈ G, (gammaLiminfRate (clampContractedRate μ₀) x : EReal)) ≤
      limsup (fun R : ℝ => ⨅ x ∈ G, (clampContractedRate μ₀ R x : EReal)) atTop := by
  have hid :=
    gammaLiminfRate_clampContractedRate_eq_cramerRateFromSanov hMGF hbdd
  have hleft :
      (⨅ x ∈ G, (gammaLiminfRate (clampContractedRate μ₀) x : EReal)) =
        ((⨅ x ∈ G, cramerRateFromSanov μ₀ x : ENNReal) : EReal) := by
    have h1 :
        (⨅ x ∈ G, (gammaLiminfRate (clampContractedRate μ₀) x : EReal)) =
          ⨅ x ∈ G, (cramerRateFromSanov μ₀ x : EReal) := by
      refine iInf_congr fun x => iInf_congr fun _ => ?_
      rw [hid x]
    have h2 :
        (⨅ x ∈ G, (cramerRateFromSanov μ₀ x : EReal)) =
          ((⨅ x ∈ G, cramerRateFromSanov μ₀ x : ENNReal) : EReal) := by
      simpa [iInf_subtype] using
        (EReal.coe_ennreal_iInf
          (fun x : G => cramerRateFromSanov μ₀ (x : EuclideanSpace ℝ (Fin d)))).symm
    exact h1.trans h2
  rw [hleft]
  have hENN :=
    iInf_cramerRateFromSanov_le_liminf_iInf_clampContractedRate hMGF hbdd hG
  have hrw : ∀ R,
      (⨅ x ∈ G, (clampContractedRate μ₀ R x : EReal)) =
        ((⨅ y ∈ G, clampContractedRate μ₀ R y : ENNReal) : EReal) := by
    intro R
    simpa [iInf_subtype] using
      (EReal.coe_ennreal_iInf
        (fun x : G => clampContractedRate μ₀ R (x : EuclideanSpace ℝ (Fin d)))).symm
  have hcoe_inf :
      ((⨅ x ∈ G, cramerRateFromSanov μ₀ x : ENNReal) : EReal) ≤
        ((liminf (fun R : ℝ => ⨅ y ∈ G, clampContractedRate μ₀ R y) atTop : ENNReal) :
          EReal) :=
    EReal.coe_ennreal_le_coe_ennreal_iff.mpr hENN
  let uE : ℝ → EReal := fun R => ⨅ x ∈ G, (clampContractedRate μ₀ R x : EReal)
  have hli_ls : liminf uE atTop ≤ limsup uE atTop :=
    @liminf_le_limsup EReal ℝ _ (atTop : Filter ℝ) inferInstance uE (by isBoundedDefault) (by isBoundedDefault)
  -- Align ENNReal-liminf coe with uE via hrw, then chain.
  have heq_li' :
      liminf uE atTop =
        ((liminf (fun R : ℝ => ⨅ y ∈ G, clampContractedRate μ₀ R y) atTop : ENNReal) : EReal) := by
    have hfun : uE = fun R => ((⨅ y ∈ G, clampContractedRate μ₀ R y : ENNReal) : EReal) := by
      funext R; exact hrw R
    simpa [hfun] using
      (EReal.liminf_coe_ennreal_eq
        (fun R : ℝ => ⨅ y ∈ G, clampContractedRate μ₀ R y))
  exact hcoe_inf.trans (heq_li'.symm.le.trans hli_ls)


/-- Non-positive radii reuse the `R = 1` clamp profile. -/
theorem clampContractedRate_eq_of_nonpos {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) {R : ℝ} (hR : ¬ 0 < R) :
    clampContractedRate μ₀ R = clampContractedRate μ₀ (1 : ℝ) := by
  funext y
  have h1 : (0 : ℝ) < 1 := one_pos
  simp [clampContractedRate, hR, h1]

/-- (4) Compact finite levels of the Γ-rate via Sanov ID. -/
theorem HasCompactFiniteLevelSets_gammaLiminfRate_clampContractedRate
    {d : ℕ} {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t)) :
    HasCompactFiniteLevelSets (gammaLiminfRate (clampContractedRate μ₀)) := by
  intro a
  have hid := funext (gammaLiminfRate_clampContractedRate_eq_cramerRateFromSanov hMGF hbdd)
  simpa [hid] using
    isCompact_cramerRateFromSanov_le_ofReal_of_HasFiniteMGF_of_forall_bddAbove μ₀ hMGF hbdd a

/-- (4) Γ-rate is an `IsRateFunction` via Sanov/CRF lsc + ID. -/
theorem IsRateFunction_gammaLiminfRate_clampContractedRate
    {d : ℕ} {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t)) :
    IsRateFunction (gammaLiminfRate (clampContractedRate μ₀)) := by
  refine ⟨?_⟩
  have heq := cramerRateFromSanov_eq_cramerRateFunction_of_tiltCover_no_hid
    μ₀ hMGF (TiltCover_of_HasFiniteMGF_of_forall_bddAbove μ₀ hMGF hbdd) hbdd
  have hLSC : LowerSemicontinuous (cramerRateFromSanov μ₀) :=
    (funext heq) ▸ lowerSemicontinuous_cramerRateFunction_of_HasFiniteMGF μ₀ hMGF hbdd
  have hid := funext (gammaLiminfRate_clampContractedRate_eq_cramerRateFromSanov hMGF hbdd)
  exact hid ▸ hLSC

/-- Bound-only open lower bound for `sampleClampMeanPi'` at every real radius. -/
theorem liminf_log_map_sampleClampMeanPi'_ge_iInf_clampContractedRate {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (R : ℝ) {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) :
    - (⨅ y ∈ U, (clampContractedRate μ₀ R y : EReal)) ≤
      liminf (fun n => ((n : ℕ) : EReal)⁻¹ *
        ENNReal.log
          ((Measure.pi fun _ : Fin n => μ₀).map
            (sampleClampMeanPi' (d := d) (n := n) R) U)) atTop := by
  by_cases hR : 0 < R
  · have hmap : ∀ n,
        sampleClampMeanPi' (d := d) (n := n) R =
          sampleClampMeanPi (d := d) (n := n) R :=
      fun n => sampleClampMeanPi'_eq_of_pos (d := d) (n := n) hR
    simp_rw [hmap]
    exact liminf_log_map_sampleClampMeanPi_ge_iInf_clampContractedRate μ₀ hR hU
  · have hmap : ∀ n,
        sampleClampMeanPi' (d := d) (n := n) R =
          sampleClampMeanPi (d := d) (n := n) 1 :=
      fun n => sampleClampMeanPi'_eq_of_nonpos (d := d) (n := n) hR
    simp_rw [hmap, clampContractedRate_eq_of_nonpos μ₀ hR]
    exact liminf_log_map_sampleClampMeanPi_ge_iInf_clampContractedRate μ₀ one_pos hU

/-- Bound-only closed upper bound for `sampleClampMeanPi'` at every real radius. -/
theorem limsup_log_map_sampleClampMeanPi'_le_iInf_clampContractedRate {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (R : ℝ) {F : Set (EuclideanSpace ℝ (Fin d))} (hF : IsClosed F) :
    limsup (fun n => ((n : ℕ) : EReal)⁻¹ *
        ENNReal.log
          ((Measure.pi fun _ : Fin n => μ₀).map
            (sampleClampMeanPi' (d := d) (n := n) R) F)) atTop ≤
      - (⨅ y ∈ F, (clampContractedRate μ₀ R y : EReal)) := by
  by_cases hR : 0 < R
  · have hmap : ∀ n,
        sampleClampMeanPi' (d := d) (n := n) R =
          sampleClampMeanPi (d := d) (n := n) R :=
      fun n => sampleClampMeanPi'_eq_of_pos (d := d) (n := n) hR
    simp_rw [hmap]
    exact limsup_log_map_sampleClampMeanPi_le_iInf_clampContractedRate μ₀ hR hF
  · have hmap : ∀ n,
        sampleClampMeanPi' (d := d) (n := n) R =
          sampleClampMeanPi (d := d) (n := n) 1 :=
      fun n => sampleClampMeanPi'_eq_of_nonpos (d := d) (n := n) hR
    simp_rw [hmap, clampContractedRate_eq_of_nonpos μ₀ hR]
    exact limsup_log_map_sampleClampMeanPi_le_iInf_clampContractedRate μ₀ one_pos hF

/-- Transfer LDP along a measure family that agrees for all `n > 0`. -/
theorem SatisfiesLDP.congr_measure_of_eventually_eq {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X]
    {μ ν : ℕ → Measure X} {I : X → ENNReal}
    (h : SatisfiesLDP μ I)
    (heq : ∀ᶠ n : ℕ in atTop, μ n = ν n) :
    SatisfiesLDP ν I := by
  refine ⟨h.isRateFunction, ?_, ?_⟩
  · intro U hU
    have hfun :
        (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n U)) =ᶠ[atTop]
          (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (ν n U)) := by
      filter_upwards [heq] with n hn; rw [hn]
    simpa [liminf_congr hfun] using h.lower_bound U hU
  · intro F hF
    have hfun :
        (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n F)) =ᶠ[atTop]
          (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (ν n F)) := by
      filter_upwards [heq] with n hn; rw [hn]
    simpa [limsup_congr hfun] using h.upper_bound F hF
