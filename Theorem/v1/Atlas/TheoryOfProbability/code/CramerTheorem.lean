/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/CramerTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.BigOperators
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Polish
import Def.ProbabilityTheory.CramerTheorem
import Lemma.Random.Integral_Sub_Log_Integral_Exp.le.ToRealKlDiv.of.Any_All_LeAbs.Continuous.Integrable_Llr
import Lemma.Random.IsProbabilityMeasure.of.Gt_0
import Lemma.Random.Measurable.of.Gt_0
import Lemma.Random.SatisfiesLDP
import Structure.v1.Atlas.TheoryOfProbability.code.LargeDeviations
import Theorem.v1.Atlas.TheoryOfProbability.code.CramerRateFunction
import Theorem.v1.Atlas.TheoryOfProbability.code.LDPContraction
open InformationTheory MeasureTheory ProbabilityTheory ProbabilityMeasure Finset Random Filter
open scoped InnerProductSpace ENNReal Topology


/-!
# Cramér's theorem via Sanov + contraction

Strategy (Atlas Lecture 13 / Body): start from Polish Sanov
`Random.SatisfiesLDP` (empirical measures, rate `klDiv · μ₀`), contract by the
barycenter map `ν ↦ ∫ x ∂ν`, then identify the contracted KL-infimum with Def's
`cramerRateFunction` (Legendre of `logMGFVec`) under exponential-moment hypotheses.

## Status

Built, sorry-free scaffolding lives here plus helpers
`LDPContraction` / `CramerRateFunction` / `CramerBarycenter` / `CramerRateID`.
The full `cramer_theorem` is **not** stated until the gaps below close without `sorry`.

* Contraction: `satisfiesLDP_map_of_continuous_of_measurable` (Giry-safe) and
  `satisfiesLDP_map_of_seqContinuous` in `LDPContraction`. Sequential barycenter
  continuity under uniform exp-moments upgrades to `Continuous` on `UniformExpMoment`
  (`CramerBarycenter`). Remaining: exponential tightness of Sanov laws into moment balls,
  or R→∞ truncation LDP via `continuous_integral_radialClamp`; Giry measurability of the
  (truncated) mean map for `Measure.map`.
* Identification `empiricalMeanMeasureVec_eq_empiricalMeanLawPi` done.
* Rate ID (`CramerRateID`): `CRF ≤ Sanov` without universal ≪/llr; tilt preserves hMGF;
  equality at tilt means under hMGF; global equality under `TiltCover`. Remaining: prove
  `TiltCover` (finite-Λ* points are tilt barycenters) by convex analysis.
-/

/-- Barycenter of a probability measure on Euclidean space (Bochner integral). -/
noncomputable def barycenter {d : ℕ} (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) :
    EuclideanSpace ℝ (Fin d) :=
  ∫ x, x ∂(ν : Measure (EuclideanSpace ℝ (Fin d)))

/-- Contracted Sanov rate: infimal KL over measures with a given barycenter. -/
noncomputable def cramerRateFromSanov {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) : ENNReal :=
  contractedRate (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
      klDiv (ν : Measure _) μ₀)
    barycenter x

/-- Sanov-shaped empirical probability measure for a positive sample size. -/
noncomputable def empiricalProbabilityMeasure {α : Type*} [MeasurableSpace α]
    {n : ℕ} (hn : 0 < n) (ω : Fin n → α) : ProbabilityMeasure α :=
  ⟨(n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i), IsProbabilityMeasure.of.Gt_0 hn⟩

/-- Product-space empirical-mean law (Sanov sample space). -/
noncomputable def empiricalMeanLawPi {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (n : ℕ) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  if 0 < n then
    (Measure.pi fun _ : Fin n => μ).map fun ω => (n : ℝ)⁻¹ • ∑ i : Fin n, ω i
  else
    μ

/-- Dirac barycenters recover the atom. -/
theorem barycenter_diracProba {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    barycenter (diracProba x) = x := by
  simp [barycenter, diracProba, integral_dirac]

/-- Finite sums of Diracs integrate the identity to the corresponding vector sum. -/
theorem integral_id_sum_dirac {d n : ℕ} (ω : Fin n → EuclideanSpace ℝ (Fin d)) :
    (∫ x, x ∂(∑ i : Fin n, Measure.dirac (ω i))) = ∑ i : Fin n, ω i := by
  have hdir : ∀ i ∈ (univ : Finset (Fin n)),
      Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) (Measure.dirac (ω i)) := by
    intro i _
    exact integrable_dirac (by simp)
  rw [integral_finsetSum_measure hdir]
  simp [integral_dirac]

/-- Fiberwise Sanov→mean identity: the barycenter of the empirical measure is the sample mean. -/
theorem barycenter_empiricalProbabilityMeasure {d n : ℕ} (hn : 0 < n)
    (ω : Fin n → EuclideanSpace ℝ (Fin d)) :
    barycenter (empiricalProbabilityMeasure hn ω) = (n : ℝ)⁻¹ • ∑ i : Fin n, ω i := by
  unfold barycenter empiricalProbabilityMeasure
  change (∫ x, x ∂((n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (ω i))) =
    (n : ℝ)⁻¹ • ∑ i : Fin n, ω i
  have hinv : ((n : ℝ≥0∞)⁻¹).toReal = (n : ℝ)⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [integral_smul_measure, integral_id_sum_dirac, hinv]

/-- The Sanov empirical-measure map, composed with barycenter, is the sample mean. -/
theorem barycenter_comp_empiricalProbabilityMeasure {d n : ℕ} (hn : 0 < n) :
    (fun ω : Fin n → EuclideanSpace ℝ (Fin d) =>
        barycenter (empiricalProbabilityMeasure hn ω)) =
      fun ω => (n : ℝ)⁻¹ • ∑ i : Fin n, ω i :=
  funext fun ω => barycenter_empiricalProbabilityMeasure hn ω

/-- On the Sanov product space, the empirical-mean law is the pushforward of the sample under the
barycenter∘empirical map — no global measurability hypothesis on `barycenter` is required. -/
theorem empiricalMeanLawPi_eq_map_barycenter_comp {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) {n : ℕ} (hn : 0 < n) :
    empiricalMeanLawPi μ n =
      (Measure.pi fun _ : Fin n => μ).map fun ω =>
        barycenter (empiricalProbabilityMeasure hn ω) := by
  simp [empiricalMeanLawPi, hn, barycenter_comp_empiricalProbabilityMeasure]

/-- On the Sanov product space, the empirical-mean law is the pushforward of the empirical-measure
law under `barycenter`, once `barycenter` is known measurable (continuity on an
exponentially tight subclass would supply this). -/
theorem empiricalMeanLawPi_eq_map_barycenter {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) {n : ℕ} (hn : 0 < n)
    (hbary : Measurable (barycenter : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) → _)) :
    empiricalMeanLawPi μ n =
      ((Measure.pi fun _ : Fin n => μ).map fun ω => empiricalProbabilityMeasure hn ω).map
        barycenter := by
  have hemp : Measurable (fun ω : Fin n → EuclideanSpace ℝ (Fin d) =>
      empiricalProbabilityMeasure hn ω) :=
    Measurable.of.Gt_0 hn
  rw [empiricalMeanLawPi_eq_map_barycenter_comp μ hn, Measure.map_map hbary hemp]
  rfl

/-- Continuous real integrals against `ProbabilityMeasure` on a compact space. -/
theorem continuous_integral_continuousMap_of_compact
    {S : Type*} [TopologicalSpace S] [CompactSpace S] [Nonempty S]
    [MeasurableSpace S] [BorelSpace S] (f : C(S, ℝ)) :
    Continuous (fun ν : ProbabilityMeasure S => ∫ x, f x ∂(ν : Measure S)) :=
  ProbabilityMeasure.continuous_integral_continuousMap f

/-- Continuous functions on a compact space are Bochner-integrable against any probability. -/
theorem Continuous.integrable_of_compactSpace_probability
    {S E : Type*} [TopologicalSpace S] [CompactSpace S]
    [MeasurableSpace S] [OpensMeasurableSpace S]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure S} [IsProbabilityMeasure μ] {f : S → E} (hf : Continuous f) :
    Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- Continuous Euclidean-valued integrals against `ProbabilityMeasure` on a compact space.

This is the compact-domain stand-in for continuity of `barycenter` used by contraction: when
measures live on (or are pushed forward from) a compact Polish space, the Bochner mean map is
continuous, hence measurable, and `satisfiesLDP_map_of_continuous` applies. The unrestricted
`ProbabilityMeasure (ℝᵈ)` case still needs UI / exponential tightness. -/
theorem continuous_integral_continuousMap_euclidean_of_compact
    {d : ℕ} {S : Type*} [TopologicalSpace S] [CompactSpace S] [Nonempty S]
    [MeasurableSpace S] [BorelSpace S]
    (ι : C(S, EuclideanSpace ℝ (Fin d))) :
    Continuous (fun ν : ProbabilityMeasure S => ∫ x, ι x ∂(ν : Measure S)) := by
  have hcoord : ∀ i : Fin d,
      Continuous (fun ν : ProbabilityMeasure S => (∫ x, ι x ∂(ν : Measure S)) i) := by
    intro i
    have hcomp : Continuous (fun ν : ProbabilityMeasure S => ∫ x, ι x i ∂(ν : Measure S)) :=
      continuous_integral_continuousMap_of_compact ⟨fun x => ι x i, by fun_prop⟩
    refine hcomp.congr fun ν => ?_
    have hint : Integrable (fun x : S => ι x) (ν : Measure S) :=
      ι.continuous.integrable_of_compactSpace_probability
    exact (eval_integral_piLp (integrable_piLp_iff.mp hint) i).symm
  have hpi : Continuous fun ν : ProbabilityMeasure S =>
      (fun i : Fin d => (∫ x, ι x ∂(ν : Measure S)) i) :=
    continuous_pi hcoord
  exact (PiLp.continuous_toLp 2 _).comp hpi

/-- Sample-mean map on the product space is continuous (hence measurable). -/
theorem continuous_empiricalMean_pi {d n : ℕ} :
    Continuous fun ω : Fin n → EuclideanSpace ℝ (Fin d) =>
      (n : ℝ)⁻¹ • ∑ i : Fin n, ω i := by
  fun_prop

/-- Under finite i.i.d. hypotheses, Def's single-space empirical-mean law matches the product-space
Sanov mean law of the common marginal. -/
theorem empiricalMeanMeasureVec_eq_empiricalMeanLawPi
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    (hX : ∀ i : Fin n, AEMeasurable (X i) μ)
    (hindep : iIndepFun (fun i : Fin n => X i) μ)
    (hid : ∀ i : Fin n, IdentDistrib (X i) (X 0) μ μ) :
    empiricalMeanMeasureVec X μ n = empiricalMeanLawPi (μ.map (X 0)) n := by
  have htuple : AEMeasurable (fun ω : Ω => fun i : Fin n => X i ω) μ :=
    AEMeasurable.of_eval hX
  have hpi : μ.map (fun ω (i : Fin n) => X i ω) =
      Measure.pi fun _ : Fin n => μ.map (X 0) := by
    rw [hindep.map_fun_eq_pi_map hX]
    congr 1
    funext i
    exact (hid i).map_eq
  have hmean : Measurable fun y : Fin n → EuclideanSpace ℝ (Fin d) =>
      (n : ℝ)⁻¹ • ∑ i : Fin n, y i :=
    continuous_empiricalMean_pi.measurable
  have hcomp :
      (fun ω : Ω => (n : ℝ)⁻¹ • ∑ i ∈ range n, X i ω) =
        (fun y : Fin n → EuclideanSpace ℝ (Fin d) => (n : ℝ)⁻¹ • ∑ i, y i) ∘
          (fun ω (i : Fin n) => X i ω) := by
    funext ω
    simp only [Function.comp_apply]
    congr 1
    exact (Fin.sum_univ_eq_sum_range (fun k => X k ω) n).symm
  simp only [empiricalMeanMeasureVec, empiricalMeanLawPi, hn, ↓reduceIte]
  rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable hmean.aemeasurable htuple, hpi]

/-- Inner product passes inside a Bochner barycenter when the identity is integrable. -/
theorem integral_inner_eq_inner_barycenter {d : ℕ}
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (t : EuclideanSpace ℝ (Fin d))
    (hint : Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) (ν : Measure _)) :
    ∫ x, ⟪t, x⟫_ℝ ∂(ν : Measure _) = ⟪t, barycenter ν⟫_ℝ := by
  simpa [barycenter, eq_comm] using (innerSL ℝ t).integral_comp_comm hint

/-- Bounded continuous DV along a fiber: Legendre integrand of a bounded inner-product test sits
below KL (hence below every contracted-rate competitor with that barycenter). -/
theorem ofReal_inner_barycenter_sub_log_le_klDiv
    {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (t : EuclideanSpace ℝ (Fin d))
    (hνμ : (ν : Measure _) ≪ μ₀)
    (hint_llr : Integrable (llr (ν : Measure _) μ₀) (ν : Measure _))
    (hint_id : Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) (ν : Measure _))
    (hC : ∃ C, ∀ x : EuclideanSpace ℝ (Fin d), |⟪t, x⟫_ℝ| ≤ C) :
    ENNReal.ofReal
        (⟪t, barycenter ν⟫_ℝ - Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀)) ≤
      klDiv (ν : Measure _) μ₀ := by
  have hf : Continuous fun x : EuclideanSpace ℝ (Fin d) => ⟪t, x⟫_ℝ := by fun_prop
  have hDV :
      ∫ x, ⟪t, x⟫_ℝ ∂(ν : Measure _) - Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀) ≤
        (klDiv (ν : Measure _) μ₀).toReal :=
    Integral_Sub_Log_Integral_Exp.le.ToRealKlDiv.of.Any_All_LeAbs.Continuous.Integrable_Llr
      hνμ hint_llr hf hC
  rw [integral_inner_eq_inner_barycenter ν t hint_id] at hDV
  exact ENNReal.ofReal_le_of_le_toReal hDV

/-- Under fiberwise absolute continuity / integrability and a bounded inner-product test, the
Legendre integrand is ≤ the contracted Sanov rate. -/
theorem ofReal_inner_sub_log_le_cramerRateFromSanov
    {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (y t : EuclideanSpace ℝ (Fin d))
    (hC : ∃ C, ∀ x : EuclideanSpace ℝ (Fin d), |⟪t, x⟫_ℝ| ≤ C)
    (hfib : ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)), barycenter ν = y →
      (ν : Measure _) ≪ μ₀ ∧
        Integrable (llr (ν : Measure _) μ₀) (ν : Measure _) ∧
        Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) (ν : Measure _)) :
    ENNReal.ofReal (⟪t, y⟫_ℝ - Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀)) ≤
      cramerRateFromSanov μ₀ y := by
  unfold cramerRateFromSanov contractedRate
  refine le_iInf₂ fun ν hν => ?_
  have hy : barycenter ν = y := by
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using hν
  obtain ⟨habs, hllr, hid⟩ := hfib ν hy
  simpa [hy] using ofReal_inner_barycenter_sub_log_le_klDiv μ₀ ν t habs hllr hid hC

/-! ### Radial clamp, finite-moment subclass, truncated means, tilting KL -/

/-- Radial clamp onto the closed ball of radius `R` (for `R ≥ 0`). -/
noncomputable def radialClamp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ) (x : E) : E :=
  (R * (R ⊔ ‖x‖)⁻¹) • x

theorem radialClamp_of_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 ≤ R) {x : E} (hx : ‖x‖ ≤ R) :
    radialClamp R x = x := by
  unfold radialClamp
  have hsup : R ⊔ ‖x‖ = R := sup_eq_left.mpr hx
  rw [hsup]
  by_cases hR0 : R = 0
  · subst hR0
    have : x = 0 := norm_le_zero_iff.mp (by simpa using hx)
    simp [this]
  · rw [mul_inv_cancel₀ hR0, one_smul]

theorem continuous_radialClamp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 < R) :
    Continuous (radialClamp (E := E) R) := by
  have hne : ∀ x : E, R ⊔ ‖x‖ ≠ 0 := fun x =>
    ne_of_gt (lt_of_lt_of_le hR le_sup_left)
  unfold radialClamp
  exact (continuous_const.mul ((continuous_const.sup continuous_norm).inv₀ hne)).smul continuous_id

theorem norm_radialClamp_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 ≤ R) (x : E) :
    ‖radialClamp R x‖ ≤ R := by
  by_cases hR0 : R = 0
  · subst hR0; simp [radialClamp]
  · by_cases hx : ‖x‖ ≤ R
    · rw [radialClamp_of_norm_le hR hx]; exact hx
    · have hxlt : R < ‖x‖ := lt_of_not_ge hx
      have hsup : R ⊔ ‖x‖ = ‖x‖ := sup_eq_right.mpr hxlt.le
      have hx0 : x ≠ 0 := by
        intro h; subst h; simp at hxlt; exact (not_lt_of_ge hR) hxlt
      unfold radialClamp
      rw [hsup, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hR (inv_nonneg.mpr (norm_nonneg _))), mul_assoc,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0), mul_one]

theorem norm_radialClamp_le_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 ≤ R) (x : E) :
    ‖radialClamp R x‖ ≤ ‖x‖ := by
  by_cases hx : ‖x‖ ≤ R
  · rw [radialClamp_of_norm_le hR hx]
  · exact (norm_radialClamp_le hR x).trans (le_of_not_ge hx)

theorem tendsto_radialClamp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
    Tendsto (fun n : ℕ => radialClamp ((n : ℝ) + 1) x) atTop (𝓝 x) := by
  refine tendsto_atTop_of_eventually_const (i₀ := Nat.ceil ‖x‖) fun n hn => ?_
  have hle : ‖x‖ ≤ (n : ℝ) + 1 := by
    calc ‖x‖ ≤ (Nat.ceil ‖x‖ : ℝ) := Nat.le_ceil _
      _ ≤ (n : ℝ) := by exact_mod_cast hn
      _ ≤ (n : ℝ) + 1 := by linarith
  exact radialClamp_of_norm_le (by positivity) hle

/-- Probability measures on `ℝᵈ` with integrable identity (finite first moment). -/
def FiniteFirstMoment (d : ℕ) : Type _ :=
  { ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) //
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.toMeasure }

namespace FiniteFirstMoment
variable {d : ℕ}
instance : Coe (FiniteFirstMoment d) (ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) where
  coe := Subtype.val
instance : TopologicalSpace (FiniteFirstMoment d) :=
  inferInstanceAs (TopologicalSpace
    { ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) //
      Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.toMeasure })
instance : MeasurableSpace (FiniteFirstMoment d) :=
  inferInstanceAs (MeasurableSpace
    { ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) //
      Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.toMeasure })
theorem integrable (ν : FiniteFirstMoment d) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) (ν : ProbabilityMeasure _).toMeasure :=
  ν.property
noncomputable def barycenterMap (ν : FiniteFirstMoment d) : EuclideanSpace ℝ (Fin d) :=
  barycenter (ν : ProbabilityMeasure _)
end FiniteFirstMoment

theorem continuous_integral_radialClamp {d : ℕ} {R : ℝ} (hR : 0 < R) :
    Continuous fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
      ∫ x, radialClamp R x ∂ν.toMeasure := by
  have hι : Continuous (radialClamp (E := EuclideanSpace ℝ (Fin d)) R) := continuous_radialClamp hR
  have hcoord : ∀ i : Fin d,
      Continuous fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) =>
        (∫ x, radialClamp R x ∂ν.toMeasure) i := by
    intro i
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
    have hbcf := ProbabilityMeasure.continuous_integral_boundedContinuousFunction f
    refine hbcf.congr fun ν => ?_
    have hint' : Integrable (fun x => radialClamp R x) ν.toMeasure :=
      Integrable.mono' (integrable_const (μ := ν.toMeasure) R) hι.aestronglyMeasurable
        (Eventually.of_forall fun x => by simpa using norm_radialClamp_le hR.le x)
    exact (eval_integral_piLp (integrable_piLp_iff.mp hint') i).symm
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi hcoord)

theorem tendsto_integral_radialClamp_barycenter {d : ℕ}
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (hint : Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.toMeasure) :
    Tendsto (fun n : ℕ => ∫ x, radialClamp ((n : ℝ) + 1) x ∂ν.toMeasure) atTop
      (𝓝 (barycenter ν)) := by
  have hmeas : ∀ n : ℕ,
      AEStronglyMeasurable (fun x => radialClamp ((n : ℝ) + 1) x) ν.toMeasure :=
    fun n => (continuous_radialClamp (Nat.cast_add_one_pos n)).aestronglyMeasurable
  refine tendsto_integral_of_dominated_convergence (μ := ν.toMeasure)
    (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖) hmeas hint.norm ?_ ?_
  · exact fun n => Eventually.of_forall fun x =>
      norm_radialClamp_le_norm (by positivity) x
  · exact Eventually.of_forall fun x => tendsto_radialClamp x

/- Sequential continuity of barycenter on `FiniteFirstMoment` along `ℕ`-indexed nets:
truncated means are continuous on all of `ProbabilityMeasure`, and DCT recovers the
barycenter under finite first moment (`tendsto_integral_radialClamp_barycenter`).
Full Borel / Giry measurability of `FiniteFirstMoment.barycenterMap` (needed for some
contraction formulations) still awaits identification of the weak topology with the
Giry σ-algebra on `ProbabilityMeasure`, or a direct Giry-measurable construction of
the truncated means; `Continuous.measurable` does not apply as stated because
`OpensMeasurableSpace (ProbabilityMeasure _)` is not available for the Giry instance. -/

/-- Exponentially tilted probability measure (when the MGF is finite). -/
noncomputable def tiltedProba {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ)
    (hf : Integrable (fun x => Real.exp (f x)) μ) :
    ProbabilityMeasure α :=
  ⟨μ.tilted f, isProbabilityMeasure_tilted hf⟩

theorem toReal_klDiv_tiltedProba {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ)
    (hf_exp : Integrable (fun x => Real.exp (f x)) μ)
    (hf : Integrable f (μ.tilted f)) :
    (klDiv (μ.tilted f) μ).toReal =
      (∫ x, f x ∂(μ.tilted f)) - Real.log (∫ x, Real.exp (f x) ∂μ) := by
  have hprob : IsProbabilityMeasure (μ.tilted f) := isProbabilityMeasure_tilted hf_exp
  have hac : μ.tilted f ≪ μ := tilted_absolutelyContinuous _ _
  have hllr_ae : llr (μ.tilted f) μ =ᵐ[μ.tilted f]
      fun x => f x - Real.log (∫ z, Real.exp (f z) ∂μ) :=
    show (fun x => Real.log (((μ.tilted f).rnDeriv μ x).toReal)) =ᵐ[μ.tilted f] _ from
      hac.ae_le (log_rnDeriv_tilted_left_self hf_exp)
  have hμeq : (μ.tilted f) Set.univ = μ Set.univ := by
    simp [hprob.measure_univ, IsProbabilityMeasure.measure_univ]
  rw [toReal_klDiv_of_measure_eq hac hμeq, integral_congr_ae hllr_ae,
    integral_sub hf (integrable_const _), integral_const]
  simp [probReal_univ]

/-- Tilting supplies a competitor for the contracted Sanov rate at the tilted barycenter. -/
theorem cramerRateFromSanov_le_of_tilted {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (t : EuclideanSpace ℝ (Fin d))
    (hf_exp : Integrable (fun x => Real.exp (⟪t, x⟫_ℝ)) μ₀)
    (hint_id : Integrable (fun x : EuclideanSpace ℝ (Fin d) => x)
      (μ₀.tilted fun x => ⟪t, x⟫_ℝ))
    (hf_inner : Integrable (fun x => ⟪t, x⟫_ℝ) (μ₀.tilted fun x => ⟪t, x⟫_ℝ)) :
    cramerRateFromSanov μ₀ (barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) hf_exp)) ≤
      ENNReal.ofReal
        (⟪t, barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) hf_exp)⟫_ℝ -
          Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀)) := by
  unfold cramerRateFromSanov contractedRate
  set ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) :=
    tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) hf_exp
  have hbary : barycenter ν = barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) hf_exp) := rfl
  refine (iInf₂_le (i := ν) (by simp [hbary])).trans_eq ?_
  have hac : ν.toMeasure ≪ μ₀ := by
    simpa [ν, tiltedProba] using tilted_absolutelyContinuous μ₀ (fun x => ⟪t, x⟫_ℝ)
  have hv : ν.toMeasure = μ₀.tilted (fun x => ⟪t, x⟫_ℝ) := by simp [ν, tiltedProba]
  have hllr_ae : llr ν.toMeasure μ₀ =ᵐ[ν.toMeasure]
      fun x => ⟪t, x⟫_ℝ - Real.log (∫ z, Real.exp (⟪t, z⟫_ℝ) ∂μ₀) := by
    rw [hv]
    exact (tilted_absolutelyContinuous μ₀ (fun x => ⟪t, x⟫_ℝ)).ae_le
      (log_rnDeriv_tilted_left_self (f := fun x => ⟪t, x⟫_ℝ) hf_exp)
  have hllr_int : Integrable (llr ν.toMeasure μ₀) ν.toMeasure :=
    (integrable_congr hllr_ae).mpr (hf_inner.sub (integrable_const _))
  have hne : klDiv ν.toMeasure μ₀ ≠ ⊤ := klDiv_ne_top hac hllr_int
  have hkl := toReal_klDiv_tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) hf_exp hf_inner
  have hinner := integral_inner_eq_inner_barycenter ν t hint_id
  change klDiv ν.toMeasure μ₀ =
    ENNReal.ofReal (⟪t, barycenter ν⟫_ℝ - Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀))
  calc
    klDiv ν.toMeasure μ₀
        = ENNReal.ofReal (klDiv ν.toMeasure μ₀).toReal := (ENNReal.ofReal_toReal hne).symm
    _ = ENNReal.ofReal
          ((∫ x, ⟪t, x⟫_ℝ ∂(μ₀.tilted fun x => ⟪t, x⟫_ℝ)) -
            Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀)) := by
          simp [ν, tiltedProba, hkl]
    _ = ENNReal.ofReal
          (⟪t, barycenter ν⟫_ℝ - Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀)) := by
          congr 1
          simp [ν, tiltedProba] at hinner ⊢
          exact hinner


/-! ### Exponential moments, unbounded DV via truncation, sequential barycenter continuity -/

/-- Finite moment generating function in every dual direction (vector hMGF). -/
def HasFiniteMGF {d : ℕ} (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ t : EuclideanSpace ℝ (Fin d), Integrable (fun x => Real.exp (⟪t, x⟫_ℝ)) μ₀

theorem HasFiniteMGF.integrable_exp {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} (h : HasFiniteMGF μ₀)
    (t : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun x => Real.exp (⟪t, x⟫_ℝ)) μ₀ :=
  h t

theorem abs_inner_radialClamp_le {d : ℕ} (t : EuclideanSpace ℝ (Fin d))
    {R : ℝ} (hR : 0 ≤ R) (x : EuclideanSpace ℝ (Fin d)) :
    |⟪t, radialClamp R x⟫_ℝ| ≤ ‖t‖ * R := by
  have hnorm := norm_radialClamp_le hR x
  calc |⟪t, radialClamp R x⟫_ℝ|
      ≤ ‖t‖ * ‖radialClamp R x‖ := by
          simpa [Real.norm_eq_abs] using abs_real_inner_le_norm t (radialClamp R x)
    _ ≤ ‖t‖ * R := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)

theorem continuous_inner_radialClamp {d : ℕ} (t : EuclideanSpace ℝ (Fin d))
    {R : ℝ} (hR : 0 < R) :
    Continuous fun x : EuclideanSpace ℝ (Fin d) => ⟪t, radialClamp R x⟫_ℝ :=
  (innerSL ℝ t).continuous.comp (continuous_radialClamp hR)

/-- Clamped barycenter integrals recover `⟪t, barycenter ν⟫` (continuous linear image of DCT). -/
theorem tendsto_integral_inner_radialClamp {d : ℕ}
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (t : EuclideanSpace ℝ (Fin d))
    (hint : Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.toMeasure) :
    Tendsto (fun n : ℕ => ∫ x, ⟪t, radialClamp ((n : ℝ) + 1) x⟫_ℝ ∂ν.toMeasure) atTop
      (𝓝 ⟪t, barycenter ν⟫_ℝ) := by
  have hclamp := tendsto_integral_radialClamp_barycenter ν hint
  have heq : ∀ n : ℕ,
      ∫ x, ⟪t, radialClamp ((n : ℝ) + 1) x⟫_ℝ ∂ν.toMeasure =
        ⟪t, ∫ x, radialClamp ((n : ℝ) + 1) x ∂ν.toMeasure⟫_ℝ := by
    intro n
    have hR : 0 < (n : ℝ) + 1 := Nat.cast_add_one_pos n
    have hint' : Integrable (fun x => radialClamp ((n : ℝ) + 1) x) ν.toMeasure :=
      Integrable.mono' (integrable_const (μ := ν.toMeasure) ((n : ℝ) + 1))
        (continuous_radialClamp hR).aestronglyMeasurable
        (Eventually.of_forall fun x => by simpa using norm_radialClamp_le hR.le x)
    simpa using (innerSL ℝ t).integral_comp_comm hint'
  exact (((innerSL ℝ t).continuous.tendsto _).comp hclamp).congr fun n => (heq n).symm

/-- `exp(⟪t, radialClamp R x⟫) ≤ exp(‖t‖ * ‖x‖)`. -/
theorem exp_inner_radialClamp_le_exp_mul_norm {d : ℕ}
    (t : EuclideanSpace ℝ (Fin d)) {R : ℝ} (hR : 0 ≤ R)
    (x : EuclideanSpace ℝ (Fin d)) :
    Real.exp (⟪t, radialClamp R x⟫_ℝ) ≤ Real.exp (‖t‖ * ‖x‖) := by
  apply Real.exp_le_exp.mpr
  have h1 : ⟪t, radialClamp R x⟫_ℝ ≤ |⟪t, radialClamp R x⟫_ℝ| := le_abs_self _
  have h2 : |⟪t, radialClamp R x⟫_ℝ| ≤ ‖t‖ * ‖radialClamp R x‖ := by
    simpa [Real.norm_eq_abs] using abs_real_inner_le_norm t (radialClamp R x)
  have h3 : ‖radialClamp R x‖ ≤ ‖x‖ := norm_radialClamp_le_norm hR x
  exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)))

/-- Integrals of `exp ∘` clamped linear tests recover the MGF under an `exp(‖t‖ ‖x‖)` dominate. -/
theorem tendsto_integral_exp_inner_radialClamp {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d)))
    (t : EuclideanSpace ℝ (Fin d))
    (hexp_id : Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (‖t‖ * ‖x‖)) μ₀)
    (hexp : Integrable (fun x => Real.exp (⟪t, x⟫_ℝ)) μ₀) :
    Tendsto (fun n : ℕ => ∫ x, Real.exp (⟪t, radialClamp ((n : ℝ) + 1) x⟫_ℝ) ∂μ₀) atTop
      (𝓝 (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀)) := by
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun x => Real.exp (⟪t, radialClamp ((n : ℝ) + 1) x⟫_ℝ)) μ₀ :=
    fun n => (Real.continuous_exp.comp
      (continuous_inner_radialClamp t (Nat.cast_add_one_pos n))).aestronglyMeasurable
  refine tendsto_integral_of_dominated_convergence
    (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (‖t‖ * ‖x‖)) hmeas hexp_id ?_ ?_
  · intro n
    exact Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
        exp_inner_radialClamp_le_exp_mul_norm t (by positivity) x
  · exact Eventually.of_forall fun x =>
      (Real.continuous_exp.tendsto _).comp
        (((innerSL ℝ t).continuous.tendsto _).comp (tendsto_radialClamp x))

/-- Unbounded linear DV: clamped DV + DCT, under an `exp(‖t‖ ‖·‖)` dominate on `μ₀`. -/
theorem ofReal_inner_barycenter_sub_log_le_klDiv_of_expNorm {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (t : EuclideanSpace ℝ (Fin d))
    (hνμ : ν.toMeasure ≪ μ₀)
    (hint_llr : Integrable (llr ν.toMeasure μ₀) ν.toMeasure)
    (hint_id : Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.toMeasure)
    (hexp : Integrable (fun x => Real.exp (⟪t, x⟫_ℝ)) μ₀)
    (hexp_id : Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (‖t‖ * ‖x‖)) μ₀) :
    ENNReal.ofReal
        (⟪t, barycenter ν⟫_ℝ - Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀)) ≤
      klDiv ν.toMeasure μ₀ := by
  have hpos : 0 < ∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀ := integral_exp_pos hexp
  have hDV_clamp : ∀ n : ℕ,
      ∫ x, ⟪t, radialClamp ((n : ℝ) + 1) x⟫_ℝ ∂ν.toMeasure -
          Real.log (∫ x, Real.exp (⟪t, radialClamp ((n : ℝ) + 1) x⟫_ℝ) ∂μ₀) ≤
        (klDiv ν.toMeasure μ₀).toReal := by
    intro n
    have hR : 0 < (n : ℝ) + 1 := Nat.cast_add_one_pos n
    exact Integral_Sub_Log_Integral_Exp.le.ToRealKlDiv.of.Any_All_LeAbs.Continuous.Integrable_Llr
      hνμ hint_llr (continuous_inner_radialClamp t hR)
      ⟨‖t‖ * ((n : ℝ) + 1), fun x => abs_inner_radialClamp_le t hR.le x⟩
  have hL := tendsto_integral_inner_radialClamp ν t hint_id
  have hRtend := tendsto_integral_exp_inner_radialClamp μ₀ t hexp_id hexp
  have hlog : Tendsto
      (fun n : ℕ => Real.log (∫ x, Real.exp (⟪t, radialClamp ((n : ℝ) + 1) x⟫_ℝ) ∂μ₀)) atTop
      (𝓝 (Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀))) :=
    (Real.continuousAt_log hpos.ne').tendsto.comp hRtend
  have hLHS : Tendsto
      (fun n : ℕ =>
        ∫ x, ⟪t, radialClamp ((n : ℝ) + 1) x⟫_ℝ ∂ν.toMeasure -
          Real.log (∫ x, Real.exp (⟪t, radialClamp ((n : ℝ) + 1) x⟫_ℝ) ∂μ₀)) atTop
      (𝓝 (⟪t, barycenter ν⟫_ℝ - Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀))) :=
    hL.sub hlog
  exact ENNReal.ofReal_le_of_le_toReal (le_of_tendsto hLHS (Eventually.of_forall hDV_clamp))

/-- Fiber form: unbounded Legendre integrand ≤ contracted Sanov rate. -/
theorem ofReal_inner_sub_log_le_cramerRateFromSanov_of_expNorm {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (y t : EuclideanSpace ℝ (Fin d))
    (hexp : Integrable (fun x => Real.exp (⟪t, x⟫_ℝ)) μ₀)
    (hexp_id : Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (‖t‖ * ‖x‖)) μ₀)
    (hfib : ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)), barycenter ν = y →
      ν.toMeasure ≪ μ₀ ∧
        Integrable (llr ν.toMeasure μ₀) ν.toMeasure ∧
        Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.toMeasure) :
    ENNReal.ofReal (⟪t, y⟫_ℝ - Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀)) ≤
      cramerRateFromSanov μ₀ y := by
  unfold cramerRateFromSanov contractedRate
  refine le_iInf₂ fun ν hν => ?_
  have hy : barycenter ν = y := by
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using hν
  obtain ⟨habs, hllr, hid⟩ := hfib ν hy
  simpa [hy] using
    ofReal_inner_barycenter_sub_log_le_klDiv_of_expNorm μ₀ ν t habs hllr hid hexp hexp_id

/-- Sequential continuity of barycenter under narrow convergence + uniform clamp tails (UI remnant). -/
theorem tendsto_barycenter_of_tendsto_of_uniform_clamp_tail {d : ℕ}
    {ν : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d))}
    {νlim : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))}
    (hlim : Tendsto ν atTop (𝓝 νlim))
    (htail : ∀ ε > 0, ∃ R : ℝ, 0 < R ∧
      (∀ n, ‖(∫ x, radialClamp R x ∂(ν n).toMeasure) - barycenter (ν n)‖ ≤ ε) ∧
        ‖(∫ x, radialClamp R x ∂νlim.toMeasure) - barycenter νlim‖ ≤ ε) :
    Tendsto (fun n => barycenter (ν n)) atTop (𝓝 (barycenter νlim)) := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨R, hRpos, htail_n, htail_lim⟩ := htail (ε / 4) (by positivity)
  have hcont := continuous_integral_radialClamp (d := d) hRpos
  have hclamp_lim := (hcont.tendsto νlim).comp hlim
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hclamp_lim (ε / 4) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 : ‖(∫ x, radialClamp R x ∂(ν n).toMeasure) -
      ∫ x, radialClamp R x ∂νlim.toMeasure‖ ≤ ε / 4 := by
    simpa [dist_eq_norm] using (hN n hn).le
  have h2 : ‖barycenter (ν n) - ∫ x, radialClamp R x ∂(ν n).toMeasure‖ ≤ ε / 4 := by
    simpa [norm_sub_rev] using htail_n n
  have h3 : ‖(∫ x, radialClamp R x ∂νlim.toMeasure) - barycenter νlim‖ ≤ ε / 4 := htail_lim
  have hsum :
      ‖barycenter (ν n) - barycenter νlim‖ ≤ ε / 4 + ε / 4 + ε / 4 := by
    have hdecomp :
        barycenter (ν n) - barycenter νlim =
          (barycenter (ν n) - ∫ x, radialClamp R x ∂(ν n).toMeasure) +
            ((∫ x, radialClamp R x ∂(ν n).toMeasure) -
              ∫ x, radialClamp R x ∂νlim.toMeasure) +
            ((∫ x, radialClamp R x ∂νlim.toMeasure) - barycenter νlim) := by
      abel
    rw [hdecomp]
    exact (norm_add₃_le).trans (by linarith)
  refine lt_of_le_of_lt hsum ?_
  linarith

/-- Pointwise Fenchel–Young competitor ≤ contracted Sanov rate, under fiber and exp-norm hyps.
Combined with `le_cramerRateFunction_of_integrable`, this yields one inequality direction for
rate identification once a `BddAbove` hypothesis unlocks the real `iSup`. -/
theorem ofReal_inner_sub_logMGF_le_cramerRateFromSanov {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (y t : EuclideanSpace ℝ (Fin d))
    (hexp : Integrable (fun x => Real.exp (⟪t, x⟫_ℝ)) μ₀)
    (hexp_id : Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (‖t‖ * ‖x‖)) μ₀)
    (hfib : ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)), barycenter ν = y →
      ν.toMeasure ≪ μ₀ ∧
        Integrable (llr ν.toMeasure μ₀) ν.toMeasure ∧
        Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.toMeasure) :
    ENNReal.ofReal (⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t) ≤
      cramerRateFromSanov μ₀ y := by
  simpa [logMGFVec_id] using
    ofReal_inner_sub_log_le_cramerRateFromSanov_of_expNorm μ₀ y t hexp hexp_id hfib

/-- At a tilt barycenter, the contracted Sanov rate matches the Fenchel–Young value of the tilt
direction (hence sits at most `cramerRateFunction`), using the tilt competitor. -/
theorem cramerRateFromSanov_le_cramerRateFunction_of_tilted {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (t : EuclideanSpace ℝ (Fin d))
    (hf_exp : Integrable (fun x => Real.exp (⟪t, x⟫_ℝ)) μ₀)
    (hint_id : Integrable (fun x : EuclideanSpace ℝ (Fin d) => x)
      (μ₀.tilted fun x => ⟪t, x⟫_ℝ))
    (hf_inner : Integrable (fun x => ⟪t, x⟫_ℝ) (μ₀.tilted fun x => ⟪t, x⟫_ℝ))
    (hbdd : BddAbove (Set.range fun s : EuclideanSpace ℝ (Fin d) =>
      ⟪s, barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) hf_exp)⟫_ℝ -
        logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ s)) :
    cramerRateFromSanov μ₀ (barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) hf_exp)) ≤
      cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀
        (barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) hf_exp)) := by
  refine (cramerRateFromSanov_le_of_tilted μ₀ t hf_exp hint_id hf_inner).trans ?_
  simpa [logMGFVec_id] using
    le_cramerRateFunction_of_integrable (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀
      (barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) hf_exp)) t hbdd


/-! ### HasFiniteMGF ⇒ exp-norm integrability, UI clamp tails, global rate inequality -/

/-- `exp(a |t|) ≤ exp(a t) + exp(-a t)`. -/
theorem exp_mul_abs_le_exp_add_exp_neg (a t : ℝ) :
    Real.exp (a * |t|) ≤ Real.exp (a * t) + Real.exp (-(a * t)) := by
  rcases le_total 0 t with ht | ht
  · simp [abs_of_nonneg ht]; linarith [Real.exp_pos (-(a * t))]
  · simp [abs_of_nonpos ht, mul_neg, neg_neg]; linarith [Real.exp_pos (a * t)]

/-- Euclidean L² ≤ `√d · ℓ∞` on coordinates. -/
theorem EuclideanSpace.norm_le_sqrt_card_mul_sup_norm {d : ℕ}
    (x : EuclideanSpace ℝ (Fin d)) (hne : (Finset.univ : Finset (Fin d)).Nonempty) :
    ‖x‖ ≤ Real.sqrt d *
      (Finset.sup' (Finset.univ : Finset (Fin d)) hne fun i => ‖x i‖) := by
  set M := Finset.sup' (Finset.univ : Finset (Fin d)) hne fun i => ‖x i‖
  have hx : ‖x‖ ^ 2 = ∑ i : Fin d, ‖x i‖ ^ 2 := by
    simpa [Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_sq_eq (𝕜 := ℝ) x
  have hsum : ∑ i : Fin d, ‖x i‖ ^ 2 ≤ ∑ i : Fin d, M ^ 2 := by
    refine Finset.sum_le_sum fun i hi =>
      pow_le_pow_left₀ (norm_nonneg _) (Finset.le_sup' (fun j => ‖x j‖) hi) 2
  have hcard : ∑ _i : Fin d, M ^ 2 = (d : ℝ) * M ^ 2 := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have hsq : ‖x‖ ^ 2 ≤ (d : ℝ) * M ^ 2 :=
    (hx.symm ▸ hsum).trans_eq hcard
  have hM0 : 0 ≤ M := by
    obtain ⟨i, hi⟩ := hne
    exact (norm_nonneg (x i)).trans (Finset.le_sup' (fun j => ‖x j‖) hi)
  have : ‖x‖ ^ 2 ≤ (Real.sqrt d * M) ^ 2 := by
    calc ‖x‖ ^ 2 ≤ (d : ℝ) * M ^ 2 := hsq
      _ = (Real.sqrt d) ^ 2 * M ^ 2 := by simp [Real.sq_sqrt (Nat.cast_nonneg _)]
      _ = (Real.sqrt d * M) ^ 2 := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hM0)).mp this

/-- Pointwise dominate of `exp(c ‖x‖)` by `1` plus a sum of two-sided coordinate MGFs
(the `+ 1` covers the `d = 0` edge case where the sum is empty). -/
theorem exp_mul_norm_le_one_add_sum_exp_coord {d : ℕ} (c : ℝ) (hc : 0 ≤ c)
    (x : EuclideanSpace ℝ (Fin d)) :
    Real.exp (c * ‖x‖) ≤
      1 + ∑ i : Fin d, (Real.exp ((c * Real.sqrt d) * x i) +
        Real.exp (-(c * Real.sqrt d) * x i)) := by
  by_cases hne : (Finset.univ : Finset (Fin d)).Nonempty
  · set M := Finset.sup' Finset.univ hne fun i : Fin d => ‖x i‖
    have hnorm : ‖x‖ ≤ Real.sqrt d * M := EuclideanSpace.norm_le_sqrt_card_mul_sup_norm x hne
    have hM0 : 0 ≤ M := by
      obtain ⟨i, hi⟩ := hne
      exact (norm_nonneg (x i)).trans (Finset.le_sup' (fun j => ‖x j‖) hi)
    have h1 : Real.exp (c * ‖x‖) ≤ Real.exp (c * Real.sqrt d * M) := by
      apply Real.exp_le_exp.mpr; nlinarith [Real.sqrt_nonneg (d : ℝ), hnorm]
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_sup' hne fun i : Fin d => ‖x i‖
    have h2 : Real.exp (c * Real.sqrt d * M) ≤
        ∑ i : Fin d, Real.exp (c * Real.sqrt d * ‖x i‖) := by
      have h := Finset.single_le_sum (fun _ _ => (Real.exp_pos _).le)
        (Finset.mem_univ i₀) (f := fun i => Real.exp (c * Real.sqrt d * ‖x i‖))
      have hMeq : M = ‖x i₀‖ := by simpa [M] using hi₀
      rw [hMeq]; exact h
    have h3 : ∀ i, Real.exp (c * Real.sqrt d * ‖x i‖) ≤
        Real.exp ((c * Real.sqrt d) * x i) + Real.exp (-(c * Real.sqrt d) * x i) := by
      intro i
      simpa [Real.norm_eq_abs, mul_assoc] using
        exp_mul_abs_le_exp_add_exp_neg (c * Real.sqrt d) (x i)
    have hsum : Real.exp (c * ‖x‖) ≤
        ∑ i, (Real.exp ((c * Real.sqrt d) * x i) +
          Real.exp (-(c * Real.sqrt d) * x i)) :=
      calc Real.exp (c * ‖x‖) ≤ Real.exp (c * Real.sqrt d * M) := h1
        _ ≤ ∑ i, Real.exp (c * Real.sqrt d * ‖x i‖) := h2
        _ ≤ ∑ i, (Real.exp ((c * Real.sqrt d) * x i) +
              Real.exp (-(c * Real.sqrt d) * x i)) :=
            Finset.sum_le_sum fun i _ => h3 i
    exact hsum.trans (le_add_of_nonneg_left zero_le_one)
  · have : IsEmpty (Fin d) :=
      Finset.univ_eq_empty_iff.mp (Finset.not_nonempty_iff_eq_empty.mp hne)
    have hx : x = 0 := Subsingleton.elim x 0
    subst hx
    simp

/-- Under vector hMGF, `exp(c ‖x‖)` is integrable for every real `c`. -/
theorem HasFiniteMGF.integrable_exp_mul_norm {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (h : HasFiniteMGF μ₀) (c : ℝ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (c * ‖x‖)) μ₀ := by
  by_cases hc : c ≤ 0
  · refine Integrable.mono' (integrable_const (μ := μ₀) (1 : ℝ))
      (by fun_prop) (Eventually.of_forall fun x => ?_)
    have : Real.exp (c * ‖x‖) ≤ 1 := by
      have : c * ‖x‖ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (norm_nonneg _)
      simpa [Real.exp_zero] using Real.exp_le_exp.mpr this
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using this
  · have hc : 0 < c := lt_of_not_ge hc
    let a : ℝ := c * Real.sqrt d
    have hpos_i : ∀ i : Fin d,
        Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (a * x i)) μ₀ := by
      intro i
      refine (h (EuclideanSpace.single i a)).congr (Eventually.of_forall fun x => ?_)
      simp [EuclideanSpace.inner_single_left]
    have hneg_i : ∀ i : Fin d,
        Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (-a * x i)) μ₀ := by
      intro i
      refine (h (EuclideanSpace.single i (-a))).congr (Eventually.of_forall fun x => ?_)
      simp [EuclideanSpace.inner_single_left]
    have hterm : ∀ i ∈ Finset.univ,
        Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
          Real.exp (a * x i) + Real.exp (-a * x i)) μ₀ :=
      fun i _ => (hpos_i i).add (hneg_i i)
    have hsum := integrable_finsetSum (μ := μ₀) Finset.univ hterm
    have hdom : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
        (1 : ℝ) + ∑ i : Fin d, (Real.exp (a * x i) + Real.exp (-a * x i))) μ₀ :=
      (integrable_const (1 : ℝ)).add hsum
    refine Integrable.mono' hdom (by fun_prop) (Eventually.of_forall fun x => ?_)
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), a] using
      exp_mul_norm_le_one_add_sum_exp_coord c hc.le x

/-- Finite first moment from hMGF (`‖x‖ ≤ exp(‖x‖)`). -/
theorem HasFiniteMGF.integrable_id {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (h : HasFiniteMGF μ₀) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ := by
  refine Integrable.mono' (h.integrable_exp_mul_norm 1)
    continuous_id.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have : ‖x‖ ≤ Real.exp ‖x‖ :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp ‖x‖)
  simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_nonneg (norm_nonneg x)] using this

/-- Norm of the radial clamp equals `min(R, ‖x‖)` for `0 ≤ R`. -/
theorem norm_radialClamp_eq_min {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 ≤ R) (x : E) :
    ‖radialClamp R x‖ = min R ‖x‖ := by
  by_cases hx : ‖x‖ ≤ R
  · rw [radialClamp_of_norm_le hR hx, min_eq_right hx]
  · have hxlt : R < ‖x‖ := lt_of_not_ge hx
    have hsup : R ⊔ ‖x‖ = ‖x‖ := sup_eq_right.mpr hxlt.le
    have hx0 : x ≠ 0 := by
      intro h; subst h; simp at hxlt
      exact (not_lt_of_ge hR) hxlt
    unfold radialClamp
    rw [hsup, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hR (inv_nonneg.mpr (norm_nonneg _))), mul_assoc,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0), mul_one, min_eq_left hxlt.le]

/-- Under `HasFiniteMGF`, every KL-finite competitor has integrable identity.
Truncation + Donsker–Varadhan gives a uniform bound on `∫ ‖radialClamp‖`; monotone
convergence upgrades to `∫ ‖x‖ < ∞`. Discharges fiber `hid` on the `{klDiv ≠ ⊤}`
branch used by CRF ≤ Sanov. -/
theorem integrable_id_of_klDiv_ne_top_of_HasFiniteMGF {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (hMGF : HasFiniteMGF μ₀)
    (hne : klDiv ν.toMeasure μ₀ ≠ ⊤) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.toMeasure := by
  have hreg := klDiv_ne_top_iff.mp hne
  have hexp : Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp ‖x‖) μ₀ := by
    simpa [one_mul] using hMGF.integrable_exp_mul_norm 1
  let B : ℝ := (klDiv ν.toMeasure μ₀).toReal + Real.log (∫ x, Real.exp ‖x‖ ∂μ₀)
  have hB : ∀ n : ℕ,
      ∫ x, ‖radialClamp ((n : ℝ) + 1) x‖ ∂ν.toMeasure ≤ B := by
    intro n
    have hR : 0 < (n : ℝ) + 1 := Nat.cast_add_one_pos n
    have hclamp_cont : Continuous (radialClamp (E := EuclideanSpace ℝ (Fin d)) ((n : ℝ) + 1)) :=
      continuous_radialClamp hR
    have hf : Continuous fun x : EuclideanSpace ℝ (Fin d) =>
        ‖radialClamp ((n : ℝ) + 1) x‖ :=
      continuous_norm.comp hclamp_cont
    have hC : ∃ C, ∀ x : EuclideanSpace ℝ (Fin d),
        |‖radialClamp ((n : ℝ) + 1) x‖| ≤ C :=
      ⟨(n : ℝ) + 1, fun x => by
        simp only [abs_of_nonneg (norm_nonneg _)]
        exact norm_radialClamp_le hR.le x⟩
    have hle :=
      Integral_Sub_Log_Integral_Exp.le.ToRealKlDiv.of.Any_All_LeAbs.Continuous.Integrable_Llr
        hreg.1 hreg.2 hf hC
    have hexp_clamp : Integrable
        (fun x => Real.exp ‖radialClamp ((n : ℝ) + 1) x‖) μ₀ :=
      Integrable.mono' hexp
        (Real.continuous_exp.comp hf).aestronglyMeasurable
        (Eventually.of_forall fun x => by
          have hexp_le : Real.exp ‖radialClamp ((n : ℝ) + 1) x‖ ≤ Real.exp ‖x‖ :=
            Real.exp_le_exp.mpr (norm_radialClamp_le_norm hR.le x)
          simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hexp_le)
    have hIntExp :
        (∫ x, Real.exp ‖radialClamp ((n : ℝ) + 1) x‖ ∂μ₀) ≤
          ∫ x, Real.exp ‖x‖ ∂μ₀ :=
      integral_mono hexp_clamp hexp fun x =>
        Real.exp_le_exp.mpr (norm_radialClamp_le_norm hR.le x)
    have hpos_clamp :
        0 < ∫ x, Real.exp ‖radialClamp ((n : ℝ) + 1) x‖ ∂μ₀ :=
      integral_exp_pos hexp_clamp
    have hlog_le :
        Real.log (∫ x, Real.exp ‖radialClamp ((n : ℝ) + 1) x‖ ∂μ₀) ≤
          Real.log (∫ x, Real.exp ‖x‖ ∂μ₀) :=
      (Real.log_le_log_iff hpos_clamp (lt_of_lt_of_le hpos_clamp hIntExp)).mpr hIntExp
    have hstep : ∫ x, ‖radialClamp ((n : ℝ) + 1) x‖ ∂ν.toMeasure ≤
        (klDiv ν.toMeasure μ₀).toReal +
          Real.log (∫ x, Real.exp ‖radialClamp ((n : ℝ) + 1) x‖ ∂μ₀) :=
      sub_le_iff_le_add.mp hle
    exact hstep.trans (add_le_add le_rfl hlog_le)
  have hlin : ∀ n : ℕ,
      ∫⁻ x, ENNReal.ofReal ‖radialClamp ((n : ℝ) + 1) x‖ ∂ν.toMeasure ≤
        ENNReal.ofReal B := by
    intro n
    have hR : 0 < (n : ℝ) + 1 := Nat.cast_add_one_pos n
    have hf : Continuous fun x : EuclideanSpace ℝ (Fin d) =>
        ‖radialClamp ((n : ℝ) + 1) x‖ :=
      continuous_norm.comp (continuous_radialClamp hR)
    have hint : Integrable (fun x => ‖radialClamp ((n : ℝ) + 1) x‖) ν.toMeasure :=
      Integrable.of_bound hf.aestronglyMeasurable ((n : ℝ) + 1)
        (Eventually.of_forall fun x => by
          simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
            using norm_radialClamp_le hR.le x)
    have hnn : 0 ≤ᵐ[ν.toMeasure] fun x => ‖radialClamp ((n : ℝ) + 1) x‖ :=
      Eventually.of_forall fun _ => norm_nonneg _
    calc ∫⁻ x, ENNReal.ofReal ‖radialClamp ((n : ℝ) + 1) x‖ ∂ν.toMeasure
        = ENNReal.ofReal (∫ x, ‖radialClamp ((n : ℝ) + 1) x‖ ∂ν.toMeasure) :=
            (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
      _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (hB n)
  have hmeas : ∀ n : ℕ, Measurable fun x : EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ‖radialClamp ((n : ℝ) + 1) x‖ := fun n => by
    have hR : 0 < (n : ℝ) + 1 := Nat.cast_add_one_pos n
    exact (continuous_norm.comp (continuous_radialClamp hR)).measurable.ennreal_ofReal
  have hmono : Monotone fun n : ℕ => fun x : EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal ‖radialClamp ((n : ℝ) + 1) x‖ := by
    intro m n hmn x
    dsimp only
    have hm : 0 ≤ (m : ℝ) + 1 := by positivity
    have hn : 0 ≤ (n : ℝ) + 1 := by positivity
    have hRle : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
    rw [norm_radialClamp_eq_min hm, norm_radialClamp_eq_min hn]
    exact ENNReal.ofReal_le_ofReal (min_le_min_right _ hRle)
  have hpt : ∀ x : EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal ‖x‖ =
        ⨆ n : ℕ, ENNReal.ofReal ‖radialClamp ((n : ℝ) + 1) x‖ := by
    intro x
    refine le_antisymm ?_ ?_
    · have hle : ‖x‖ ≤ (Nat.ceil ‖x‖ : ℝ) + 1 := by
        calc ‖x‖ ≤ (Nat.ceil ‖x‖ : ℝ) := Nat.le_ceil _
          _ ≤ (Nat.ceil ‖x‖ : ℝ) + 1 := by linarith
      have hR : 0 ≤ (Nat.ceil ‖x‖ : ℝ) + 1 := by positivity
      have hxeq : ENNReal.ofReal ‖x‖ =
          ENNReal.ofReal ‖radialClamp ((Nat.ceil ‖x‖ : ℝ) + 1) x‖ := by
        rw [radialClamp_of_norm_le hR hle]
      rw [hxeq]
      exact le_iSup (fun n : ℕ =>
          ENNReal.ofReal ‖radialClamp ((n : ℝ) + 1) x‖) (Nat.ceil ‖x‖)
    · exact iSup_le fun n => by
        have hR : 0 ≤ (n : ℝ) + 1 := by positivity
        exact ENNReal.ofReal_le_ofReal (norm_radialClamp_le_norm hR x)
  have hsup : ∫⁻ x, ENNReal.ofReal ‖x‖ ∂ν.toMeasure =
      ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal ‖radialClamp ((n : ℝ) + 1) x‖ ∂ν.toMeasure := by
    have hcongr : ∫⁻ x, ENNReal.ofReal ‖x‖ ∂ν.toMeasure =
        ∫⁻ x, ⨆ n : ℕ, ENNReal.ofReal ‖radialClamp ((n : ℝ) + 1) x‖ ∂ν.toMeasure :=
      lintegral_congr fun x => hpt x
    rw [hcongr, lintegral_iSup hmeas hmono]
  have hfin : ∫⁻ x, ENNReal.ofReal ‖x‖ ∂ν.toMeasure ≤ ENNReal.ofReal B := by
    rw [hsup]
    exact iSup_le hlin
  refine ⟨continuous_id.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  exact lt_of_le_of_lt hfin ENNReal.ofReal_lt_top

/-- Global fiber helper under `HasFiniteMGF`: KL-finite Sanov competitors are integrable. -/
theorem integrable_id_of_barycenter_eq_of_HasFiniteMGF {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (y : EuclideanSpace ℝ (Fin d))
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (_hy : barycenter ν = y)
    (hne : klDiv ν.toMeasure μ₀ ≠ ⊤) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.toMeasure :=
  integrable_id_of_klDiv_ne_top_of_HasFiniteMGF μ₀ ν hMGF hne


/-- Pointwise clamp residual vs exponential moment. -/
theorem norm_sub_radialClamp_le_exp_moment {d : ℕ}
    {c R : ℝ} (hc : 0 < c) (hR : 0 < R) (x : EuclideanSpace ℝ (Fin d)) :
    ‖x - radialClamp R x‖ ≤
      (2 / c) * Real.exp (-c * R) * Real.exp ((2 * c) * ‖x‖) := by
  by_cases hx : ‖x‖ ≤ R
  · have : radialClamp R x = x := radialClamp_of_norm_le hR.le hx
    simp only [this, sub_self, norm_zero]
    positivity
  · have hx' : R < ‖x‖ := lt_of_not_ge hx
    have htwo : ‖x - radialClamp R x‖ ≤ 2 * ‖x‖ := by
      calc ‖x - radialClamp R x‖ ≤ ‖x‖ + ‖radialClamp R x‖ := norm_sub_le _ _
        _ ≤ ‖x‖ + R := add_le_add le_rfl (norm_radialClamp_le hR.le x)
        _ ≤ ‖x‖ + ‖x‖ := add_le_add le_rfl hx'.le
        _ = 2 * ‖x‖ := by ring
    have hc0 : c ≠ 0 := hc.ne'
    have hx_le : ‖x‖ ≤ c⁻¹ * Real.exp (c * ‖x‖) := by
      have h1 : c * ‖x‖ ≤ Real.exp (c * ‖x‖) :=
        (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
      calc ‖x‖ = c⁻¹ * (c * ‖x‖) := by field_simp
        _ ≤ c⁻¹ * Real.exp (c * ‖x‖) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hc.le)
    have hexp_split :
        Real.exp (c * ‖x‖) ≤ Real.exp (-c * R) * Real.exp ((2 * c) * ‖x‖) := by
      have hrew : Real.exp (c * ‖x‖) =
          Real.exp (-c * ‖x‖) * Real.exp ((2 * c) * ‖x‖) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hrew]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      -- `-c * ‖x‖ ≤ -c * R` since `c > 0` and `R < ‖x‖`.
      exact Real.exp_le_exp.mpr <| by nlinarith
    calc ‖x - radialClamp R x‖ ≤ 2 * ‖x‖ := htwo
      _ ≤ 2 * (c⁻¹ * Real.exp (c * ‖x‖)) :=
          mul_le_mul_of_nonneg_left hx_le (by positivity)
      _ = (2 / c) * Real.exp (c * ‖x‖) := by field_simp [hc0]
      _ ≤ (2 / c) * (Real.exp (-c * R) * Real.exp ((2 * c) * ‖x‖)) :=
          mul_le_mul_of_nonneg_left hexp_split (div_nonneg (by norm_num : (0:ℝ) ≤ 2) hc.le)
      _ = (2 / c) * Real.exp (-c * R) * Real.exp ((2 * c) * ‖x‖) := by ring

/-- Integrated clamp residual under an `exp(2c ‖·‖)` moment. -/
theorem norm_barycenter_sub_integral_radialClamp_le {d : ℕ}
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    {c R : ℝ} (hc : 0 < c) (hR : 0 < R)
    (hint : Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.toMeasure)
    (hexp : Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp ((2 * c) * ‖x‖))
      ν.toMeasure) :
    ‖barycenter ν - ∫ x, radialClamp R x ∂ν.toMeasure‖ ≤
      (2 / c) * Real.exp (-c * R) * ∫ x, Real.exp ((2 * c) * ‖x‖) ∂ν.toMeasure := by
  have hclamp_int : Integrable (fun x => radialClamp R x) ν.toMeasure :=
    Integrable.mono' (integrable_const (μ := ν.toMeasure) R)
      (continuous_radialClamp hR).aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa using norm_radialClamp_le hR.le x)
  have hdecomp : barycenter ν - ∫ x, radialClamp R x ∂ν.toMeasure =
      ∫ x, (x - radialClamp R x) ∂ν.toMeasure := by
    simp [barycenter, integral_sub hint hclamp_int]
  rw [hdecomp]
  refine (norm_integral_le_integral_norm (fun x => x - radialClamp R x)).trans ?_
  set C : ℝ := (2 / c) * Real.exp (-c * R)
  have hpt : ∀ x, ‖x - radialClamp R x‖ ≤ C * Real.exp ((2 * c) * ‖x‖) := fun x => by
    simpa [C, mul_assoc] using norm_sub_radialClamp_le_exp_moment (d := d) hc hR x
  have hint_bound : Integrable
      (fun x : EuclideanSpace ℝ (Fin d) => C * Real.exp ((2 * c) * ‖x‖)) ν.toMeasure :=
    hexp.const_mul C
  refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
    hint_bound (Eventually.of_forall hpt)).trans_eq ?_
  rw [integral_const_mul]


/-- Choose `R > 0` so that `(2/c) exp(-c R) M ≤ ε`. -/
theorem exists_radius_exp_tail_le {c M ε : ℝ} (hc : 0 < c) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ (2 / c) * Real.exp (-c * R) * M ≤ ε := by
  by_cases hM0 : M = 0
  · refine ⟨1, one_pos, ?_⟩
    simp [hM0]
    exact hε.le
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
    have hc0 : c ≠ 0 := hc.ne'
    -- Choose R so exp(c R) ≥ 1+K with K = (2/c) M / ε.
    let K : ℝ := (2 / c) * M / ε
    have hK : 0 < K := by
      have : 0 < 2 / c := div_pos (by norm_num : (0:ℝ) < 2) hc
      exact div_pos (mul_pos this hMpos) hε
    have h1K : 0 < 1 + K := by linarith
    let R : ℝ := 1 + c⁻¹ * Real.log (1 + K)
    have hRpos : 0 < R := by
      have hlog : 0 ≤ Real.log (1 + K) := Real.log_nonneg (by linarith)
      have : 0 ≤ c⁻¹ * Real.log (1 + K) :=
        mul_nonneg (inv_nonneg.mpr hc.le) hlog
      linarith
    refine ⟨R, hRpos, ?_⟩
    have hcR : c * R = c + Real.log (1 + K) := by
      change c * (1 + c⁻¹ * Real.log (1 + K)) = c + Real.log (1 + K)
      field_simp [hc0]
    have hexp_eq :
        Real.exp (-c * R) = Real.exp (-c) * (1 + K)⁻¹ := by
      have hneg : -c * R = -(c + Real.log (1 + K)) := by
        calc -c * R = -(c * R) := by ring
          _ = -(c + Real.log (1 + K)) := by rw [hcR]
      calc Real.exp (-c * R)
          = Real.exp (-(c + Real.log (1 + K))) := by rw [hneg]
        _ = Real.exp (-c + -Real.log (1 + K)) := by rw [neg_add]
        _ = Real.exp (-c) * Real.exp (-Real.log (1 + K)) := Real.exp_add _ _
        _ = Real.exp (-c) * (Real.exp (Real.log (1 + K)))⁻¹ := by
            rw [Real.exp_neg (Real.log (1 + K))]
        _ = Real.exp (-c) * (1 + K)⁻¹ := by rw [Real.exp_log h1K]
    have hexp_le : Real.exp (-c * R) ≤ (1 + K)⁻¹ := by
      have h3 : Real.exp (-c) ≤ 1 := (Real.exp_le_one_iff).2 (neg_nonpos.mpr hc.le)
      calc Real.exp (-c * R) = Real.exp (-c) * (1 + K)⁻¹ := hexp_eq
        _ ≤ 1 * (1 + K)⁻¹ :=
            mul_le_mul_of_nonneg_right h3 (inv_nonneg.mpr h1K.le)
        _ = (1 + K)⁻¹ := one_mul _
    have hcoeff : 0 ≤ 2 / c := div_nonneg (by norm_num : (0:ℝ) ≤ 2) hc.le
    have hstep1 :
        (2 / c) * Real.exp (-c * R) * M ≤ (2 / c) * (1 + K)⁻¹ * M :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp_le hcoeff) hM
    refine hstep1.trans ?_
    have hinv : (1 + K)⁻¹ ≤ K⁻¹ := inv_anti₀ hK (by linarith : K ≤ 1 + K)
    have hstep2 :
        (2 / c) * (1 + K)⁻¹ * M ≤ (2 / c) * K⁻¹ * M :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinv hcoeff) hM
    refine hstep2.trans_eq ?_
    -- (2/c) * K⁻¹ * M = ε
    have hKdef : K = (2 / c) * M / ε := rfl
    calc (2 / c) * K⁻¹ * M
        = (2 / c) * ((2 / c) * M / ε)⁻¹ * M := by rw [hKdef]
      _ = ε := by field_simp [hc0, hMpos.ne', hε.ne']

/-- Uniform clamp tails from a uniform exponential-moment bound along a sequence + limit. -/
theorem uniform_clamp_tail_of_uniform_exp_moment {d : ℕ}
    {ν : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d))}
    {νlim : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))}
    {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hint : ∀ n, Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) (ν n).toMeasure)
    (hint_lim : Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) νlim.toMeasure)
    (hexp : ∀ n, Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp ((2 * c) * ‖x‖))
      (ν n).toMeasure)
    (hexp_lim : Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp ((2 * c) * ‖x‖))
      νlim.toMeasure)
    (hbound : ∀ n, ∫ x, Real.exp ((2 * c) * ‖x‖) ∂(ν n).toMeasure ≤ M)
    (hbound_lim : ∫ x, Real.exp ((2 * c) * ‖x‖) ∂νlim.toMeasure ≤ M) :
    ∀ ε > 0, ∃ R : ℝ, 0 < R ∧
      (∀ n, ‖(∫ x, radialClamp R x ∂(ν n).toMeasure) - barycenter (ν n)‖ ≤ ε) ∧
        ‖(∫ x, radialClamp R x ∂νlim.toMeasure) - barycenter νlim‖ ≤ ε := by
  intro ε hε
  obtain ⟨R, hRpos, hcoeff⟩ := exists_radius_exp_tail_le hc hM hε
  refine ⟨R, hRpos, ?_, ?_⟩
  · intro n
    have hle := norm_barycenter_sub_integral_radialClamp_le (ν n) hc hRpos (hint n) (hexp n)
    have : ‖barycenter (ν n) - ∫ x, radialClamp R x ∂(ν n).toMeasure‖ ≤
        (2 / c) * Real.exp (-c * R) * M :=
      hle.trans <| mul_le_mul_of_nonneg_left (hbound n) <| by positivity
    simpa [norm_sub_rev] using this.trans hcoeff
  · have hle := norm_barycenter_sub_integral_radialClamp_le νlim hc hRpos hint_lim hexp_lim
    have : ‖barycenter νlim - ∫ x, radialClamp R x ∂νlim.toMeasure‖ ≤
        (2 / c) * Real.exp (-c * R) * M :=
      hle.trans <| mul_le_mul_of_nonneg_left hbound_lim <| by positivity
    simpa [norm_sub_rev] using this.trans hcoeff

/-- Sequential continuity of barycenter under narrow convergence + uniform exp-moment bound. -/
theorem tendsto_barycenter_of_tendsto_of_uniform_exp_moment {d : ℕ}
    {ν : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d))}
    {νlim : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))}
    {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hlim : Tendsto ν atTop (𝓝 νlim))
    (hint : ∀ n, Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) (ν n).toMeasure)
    (hint_lim : Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) νlim.toMeasure)
    (hexp : ∀ n, Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp ((2 * c) * ‖x‖))
      (ν n).toMeasure)
    (hexp_lim : Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp ((2 * c) * ‖x‖))
      νlim.toMeasure)
    (hbound : ∀ n, ∫ x, Real.exp ((2 * c) * ‖x‖) ∂(ν n).toMeasure ≤ M)
    (hbound_lim : ∫ x, Real.exp ((2 * c) * ‖x‖) ∂νlim.toMeasure ≤ M) :
    Tendsto (fun n => barycenter (ν n)) atTop (𝓝 (barycenter νlim)) :=
  tendsto_barycenter_of_tendsto_of_uniform_clamp_tail hlim
    (uniform_clamp_tail_of_uniform_exp_moment hc hM hint hint_lim hexp hexp_lim
      hbound hbound_lim)

/-- Global Legendre ≤ contracted Sanov under fiberwise DV + BddAbove (via `ofReal_ciSup_le`). -/
theorem cramerRateFunction_le_cramerRateFromSanov {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (y : EuclideanSpace ℝ (Fin d))
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
      ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t))
    (hfib : ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)), barycenter ν = y →
      ν.toMeasure ≪ μ₀ ∧
        Integrable (llr ν.toMeasure μ₀) ν.toMeasure ∧
        Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.toMeasure) :
    cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y ≤
      cramerRateFromSanov μ₀ y := by
  refine cramerRateFunction_le_of_forall_ofReal_inner_sub_logMGF_le
    (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y _ hbdd fun t => ?_
  exact ofReal_inner_sub_logMGF_le_cramerRateFromSanov μ₀ y t (hMGF t)
    (hMGF.integrable_exp_mul_norm ‖t‖) hfib

/-- Rate equality at a tilt barycenter: Sanov contraction = Cramér rate. -/
theorem cramerRateFromSanov_eq_cramerRateFunction_of_tilted {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (t : EuclideanSpace ℝ (Fin d))
    (hMGF : HasFiniteMGF μ₀)
    (hint_id : Integrable (fun x : EuclideanSpace ℝ (Fin d) => x)
      (μ₀.tilted fun x => ⟪t, x⟫_ℝ))
    (hf_inner : Integrable (fun x => ⟪t, x⟫_ℝ) (μ₀.tilted fun x => ⟪t, x⟫_ℝ))
    (hbdd : BddAbove (Set.range fun s : EuclideanSpace ℝ (Fin d) =>
      ⟪s, barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))⟫_ℝ -
        logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ s))
    (hfib : ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      barycenter ν = barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t)) →
        ν.toMeasure ≪ μ₀ ∧
          Integrable (llr ν.toMeasure μ₀) ν.toMeasure ∧
          Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.toMeasure) :
    cramerRateFromSanov μ₀ (barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))) =
      cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀
        (barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))) := by
  refine le_antisymm ?_ ?_
  · exact cramerRateFromSanov_le_cramerRateFunction_of_tilted μ₀ t (hMGF t)
      hint_id hf_inner hbdd
  · exact cramerRateFunction_le_cramerRateFromSanov μ₀ _ hMGF hbdd hfib
