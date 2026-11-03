/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/CramerTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Sequences
import Theorem.v1.Atlas.TheoryOfProbability.code.CramerTheorem
import Theorem.v1.Atlas.TheoryOfProbability.code.CramerRateID
import Theorem.v1.Atlas.TheoryOfProbability.code.LDPContraction
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
contracts to the empirical-mean LDP with rate `cramerRateFromSanov`. This is exactly
the `hLDP` hypothesis of `cramer_theorem_of_HasFiniteMGF_of_forall_bddAbove`.

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

/-- Random-facing: `HasFiniteMGF` + `forall_bddAbove` + named residual `HasEmpiricalMeanSanovLDP`.
Same as `cramer_theorem_of_HasFiniteMGF_of_forall_bddAbove` with `hLDP` packaged. -/
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
  cramer_theorem_of_HasFiniteMGF_of_forall_bddAbove μ₀ hMGF hbdd hLDP

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

/-! ### Remaining gap (Dembo-Zeitouni 4.2.16 LDP transfer)

Landed under `HasFiniteMGF` + `forall_bddAbove`: Gamma-bundle, exp-good / diagonal
`ExpEquivalentMaps`, compact finite CRF/Sanov levels, fixed-R clamp LDP (needs `hJ`).

New in `LDPContraction` (DZ 4.2.13 / 4.1.6): bound-only contraction
(`limsup`/`liminf_log_map_*_iInf_contractedRate`, no `hJ`),
`preimage_subset_cthickening_union_dist`, `limsup_inv_mul_log_add_le_max`,
`limsup_log_map_le_iInf_cthickening_of_ExpEquivalentMaps`,
`HasCompactFiniteLevelSets`, `iInf_cthickening_le_iInf`,
`exists_mem_cthickening_le_ofReal_add_one`,
`exists_mem_cthickening_le_ofReal_add`,
**`iInf_le_iSup_iInf_cthickening` / `iSup_iInf_cthickening_eq_iInf`** (thickening recovery),
`GammaLiminf` / `GammaLiminfReal` predicates.

**Exact remaining math gap for discharging `hLDP`:**
1. ~~thickening recovery~~ (landed);
2. `satisfiesLDP_of_ExpEquivalentMaps` (same good rate; DZ 4.2.13): finish EReal
   `⨅_ε (-inf_{F^ε}) = -inf_F` wire on top of recovery + open lower bounds via balls
   with exp-equivalent error (`limsup` bot on distance sets);
3. `satisfiesLDP_of_EventuallyExpGoodApprox` / `satisfiesLDP_of_gammaApprox`
   (DZ 4.2.16): set-infima `liminf_R inf_G I_R >= inf_G I` from sequential Gamma-liminf
   + coercive compact levels of `I_R` (via clamp-Legendre <= I_R + uniform MGF modulus),
   then specialize with bound-only clamp contraction + exp-good + Gamma-bundle;
4. drop `hLDP` from `cramer_theorem_of_HasFiniteMGF_of_forall_bddAbove`.
Wrapper still carries `hLDP`; do not ping Random yet.
-/
