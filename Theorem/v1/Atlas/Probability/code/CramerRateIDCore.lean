/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/CramerTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Moments.Tilted
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.InnerProductSpace.Continuous
import Theorem.v1.Atlas.Probability.code.CramerRateFunction
import Theorem.v1.Atlas.Probability.code.CramerTheorem
open InformationTheory MeasureTheory ProbabilityMeasure ProbabilityTheory Filter
open scoped InnerProductSpace ENNReal Topology

/-!
# Rate identification core: contracted Sanov ↔ Cramér Legendre

Core lemmas for `CramerRateID` / `CramerBarycenter` (no DZ mean-LDP entry).

Strengthens the tilt-fiber glue in `CramerTheorem` toward a global equality
`cramerRateFromSanov = cramerRateFunction` under `HasFiniteMGF`.

## Status

* `CRF ≤ Sanov` without a universal fiber hypothesis: irregular measures have `klDiv = ∞`.
* Tilting preserves `HasFiniteMGF`; tilt equality cleans up under `hMGF` alone (+ `BddAbove`).
* Global equality under an explicit tilt-covering of `{y | CRF y < ∞}`.
* Residual: prove the covering (every finite-Λ* point is a tilt barycenter) by convex analysis
  / essential smoothness of `logMGFVec` under vector hMGF.
-/

/-- Tilting by a dual direction preserves vector exponential moments. -/
theorem HasFiniteMGF.tilted {d : ℕ}
    {μ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ₀]
    (h : HasFiniteMGF μ₀) (t : EuclideanSpace ℝ (Fin d)) :
    HasFiniteMGF (μ₀.tilted fun x => ⟪t, x⟫_ℝ) := by
  intro s
  have ht : Integrable (fun x => Real.exp (⟪t, x⟫_ℝ)) μ₀ := h t
  -- `Integrable (exp ⟨s,·⟩) (tilt t) ↔ Integrable (exp⟨t,·⟩ • exp⟨s,·⟩) μ₀`.
  rw [integrable_tilted_iff (E := ℝ) ht]
  refine (h (s + t)).congr (Filter.Eventually.of_forall fun x => ?_)
  simp [smul_eq_mul, Real.exp_add, inner_add_left, mul_comm]

/-- Fiber Legendre integrand ≤ contracted Sanov rate, with no universal regularity hypothesis:
measures that fail absolute continuity / llr-integrability contribute `klDiv = ∞`. -/
theorem ofReal_inner_sub_log_le_cramerRateFromSanov_of_expNorm_of_integrableId {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (y t : EuclideanSpace ℝ (Fin d))
    (hexp : Integrable (fun x => Real.exp (⟪t, x⟫_ℝ)) μ₀)
    (hexp_id : Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (‖t‖ * ‖x‖)) μ₀)
    (hid : ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      barycenter ν = y → Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.toMeasure) :
    ENNReal.ofReal (⟪t, y⟫_ℝ - Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀)) ≤
      cramerRateFromSanov μ₀ y := by
  unfold cramerRateFromSanov contractedRate
  refine le_iInf₂ fun ν hν => ?_
  have hy : barycenter ν = y := by
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using hν
  have hint_id := hid ν hy
  by_cases hne : klDiv ν.toMeasure μ₀ ≠ ⊤
  · have hreg := klDiv_ne_top_iff.mp hne
    simpa [hy] using
      ofReal_inner_barycenter_sub_log_le_klDiv_of_expNorm μ₀ ν t hreg.1 hreg.2 hint_id hexp hexp_id
  · have htop : klDiv ν.toMeasure μ₀ = ⊤ := not_ne_iff.mp hne
    simpa [htop] using (le_top :
      ENNReal.ofReal (⟪t, y⟫_ℝ - Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀)) ≤ ⊤)

/-- Fiber Legendre ≤ contracted Sanov under `HasFiniteMGF` alone (fiber `hid` internalized
via `integrable_id_of_klDiv_ne_top_of_HasFiniteMGF`). -/
theorem ofReal_inner_sub_log_le_cramerRateFromSanov_of_HasFiniteMGF {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (y t : EuclideanSpace ℝ (Fin d))
    (hMGF : HasFiniteMGF μ₀) :
    ENNReal.ofReal (⟪t, y⟫_ℝ - Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀)) ≤
      cramerRateFromSanov μ₀ y := by
  unfold cramerRateFromSanov contractedRate
  refine le_iInf₂ fun ν hν => ?_
  have hy : barycenter ν = y := by
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using hν
  by_cases hne : klDiv ν.toMeasure μ₀ ≠ ⊤
  · have hreg := klDiv_ne_top_iff.mp hne
    have hint_id := integrable_id_of_klDiv_ne_top_of_HasFiniteMGF μ₀ ν hMGF hne
    simpa [hy] using
      ofReal_inner_barycenter_sub_log_le_klDiv_of_expNorm μ₀ ν t hreg.1 hreg.2 hint_id
        (hMGF t) (hMGF.integrable_exp_mul_norm ‖t‖)
  · have htop : klDiv ν.toMeasure μ₀ = ⊤ := not_ne_iff.mp hne
    simpa [htop] using (le_top :
      ENNReal.ofReal (⟪t, y⟫_ℝ - Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀)) ≤ ⊤)

/-- Global `CRF ≤ Sanov` under hMGF + integrable-id on fibers (no ≪ / llr universal hyp). -/
theorem cramerRateFunction_le_cramerRateFromSanov_of_integrableId {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (y : EuclideanSpace ℝ (Fin d))
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
      ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t))
    (hid : ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      barycenter ν = y → Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.toMeasure) :
    cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y ≤
      cramerRateFromSanov μ₀ y := by
  refine cramerRateFunction_le_of_forall_ofReal_inner_sub_logMGF_le
    (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y _ hbdd fun t => ?_
  simpa [logMGFVec_id] using
    ofReal_inner_sub_log_le_cramerRateFromSanov_of_expNorm_of_integrableId μ₀ y t
      (hMGF t) (hMGF.integrable_exp_mul_norm ‖t‖) hid

/-- Global `CRF ≤ Sanov` under `HasFiniteMGF` alone (`hid` internalized). -/
theorem cramerRateFunction_le_cramerRateFromSanov_of_HasFiniteMGF {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (y : EuclideanSpace ℝ (Fin d))
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
      ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t)) :
    cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y ≤
      cramerRateFromSanov μ₀ y := by
  refine cramerRateFunction_le_of_forall_ofReal_inner_sub_logMGF_le
    (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y _ hbdd fun t => ?_
  simpa [logMGFVec_id] using
    ofReal_inner_sub_log_le_cramerRateFromSanov_of_HasFiniteMGF μ₀ y t hMGF

/-- Tilt competitor ≤ CRF, with integrable-id/inner discharged from hMGF on the tilt. -/
theorem cramerRateFromSanov_le_cramerRateFunction_of_tilted_of_HasFiniteMGF {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (t : EuclideanSpace ℝ (Fin d))
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : BddAbove (Set.range fun s : EuclideanSpace ℝ (Fin d) =>
      ⟪s, barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))⟫_ℝ -
        logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ s)) :
    cramerRateFromSanov μ₀ (barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))) ≤
      cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀
        (barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))) := by
  haveI : IsProbabilityMeasure (μ₀.tilted fun x => ⟪t, x⟫_ℝ) :=
    isProbabilityMeasure_tilted (hMGF t)
  have htiltMGF := hMGF.tilted t
  have hint_id := htiltMGF.integrable_id
  have hf_inner : Integrable (fun x => ⟪t, x⟫_ℝ) (μ₀.tilted fun x => ⟪t, x⟫_ℝ) :=
    (innerSL ℝ t).integrable_comp hint_id
  exact cramerRateFromSanov_le_cramerRateFunction_of_tilted μ₀ t (hMGF t)
    hint_id hf_inner hbdd

/-- Rate equality at every tilt barycenter under hMGF (+ BddAbove + id on Sanov fibers). -/
theorem cramerRateFromSanov_eq_cramerRateFunction_of_tilted_of_HasFiniteMGF {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (t : EuclideanSpace ℝ (Fin d))
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : BddAbove (Set.range fun s : EuclideanSpace ℝ (Fin d) =>
      ⟪s, barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))⟫_ℝ -
        logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ s))
    (hid : ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      barycenter ν = barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t)) →
        Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.toMeasure) :
    cramerRateFromSanov μ₀ (barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))) =
      cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀
        (barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))) := by
  refine le_antisymm ?_ ?_
  · exact cramerRateFromSanov_le_cramerRateFunction_of_tilted_of_HasFiniteMGF μ₀ t hMGF hbdd
  · exact cramerRateFunction_le_cramerRateFromSanov_of_integrableId μ₀ _ hMGF hbdd hid

/-- Rate equality at tilt barycenters under `HasFiniteMGF` + `BddAbove` (`hid` internalized). -/
theorem cramerRateFromSanov_eq_cramerRateFunction_of_tilted_of_HasFiniteMGF_no_hid {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (t : EuclideanSpace ℝ (Fin d))
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : BddAbove (Set.range fun s : EuclideanSpace ℝ (Fin d) =>
      ⟪s, barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))⟫_ℝ -
        logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ s)) :
    cramerRateFromSanov μ₀ (barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))) =
      cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀
        (barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))) := by
  refine le_antisymm ?_ ?_
  · exact cramerRateFromSanov_le_cramerRateFunction_of_tilted_of_HasFiniteMGF μ₀ t hMGF hbdd
  · exact cramerRateFunction_le_cramerRateFromSanov_of_HasFiniteMGF μ₀ _ hMGF hbdd

/-- Covering hypothesis: every point of finite Cramér rate is a tilt barycenter. -/
def TiltCover {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀) : Prop :=
  ∀ y : EuclideanSpace ℝ (Fin d),
    cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y < ∞ →
      ∃ t : EuclideanSpace ℝ (Fin d),
        barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t)) = y

/-- Global rate equality from tilt covering of the finite-Λ* set.
When `CRF y = ∞`, the inequality `CRF ≤ Sanov` forces `Sanov y = ∞`. -/
theorem cramerRateFromSanov_eq_cramerRateFunction_of_tiltCover {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hcover : TiltCover μ₀ hMGF)
    (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t))
    (hid : ∀ y : EuclideanSpace ℝ (Fin d),
      ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
        barycenter ν = y → Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.toMeasure) :
    ∀ y : EuclideanSpace ℝ (Fin d),
      cramerRateFromSanov μ₀ y =
        cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y := by
  intro y
  refine le_antisymm ?_ ?_
  · -- Sanov ≤ CRF
    by_cases hy : cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y < ∞
    · obtain ⟨t, ht⟩ := hcover y hy
      have heq := cramerRateFromSanov_eq_cramerRateFunction_of_tilted_of_HasFiniteMGF
        μ₀ t hMGF (hbdd _) (fun ν hν => hid _ ν (ht ▸ hν))
      rw [← ht]
      exact heq.le
    · have : cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y = ∞ :=
        le_antisymm le_top (not_lt.mp hy)
      simpa [this] using (le_top : cramerRateFromSanov μ₀ y ≤ ⊤)
  · exact cramerRateFunction_le_cramerRateFromSanov_of_integrableId μ₀ y hMGF (hbdd y) (hid y)

/-- Global rate equality under `TiltCover` + `HasFiniteMGF` + `hbdd` (`hid` internalized). -/
theorem cramerRateFromSanov_eq_cramerRateFunction_of_tiltCover_no_hid {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hcover : TiltCover μ₀ hMGF)
    (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t)) :
    ∀ y : EuclideanSpace ℝ (Fin d),
      cramerRateFromSanov μ₀ y =
        cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y := by
  intro y
  refine le_antisymm ?_ ?_
  · by_cases hy : cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y < ∞
    · obtain ⟨t, ht⟩ := hcover y hy
      have heq := cramerRateFromSanov_eq_cramerRateFunction_of_tilted_of_HasFiniteMGF_no_hid
        μ₀ t hMGF (hbdd _)
      rw [← ht]
      exact heq.le
    · have : cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y = ∞ :=
        le_antisymm le_top (not_lt.mp hy)
      simpa [this] using (le_top : cramerRateFromSanov μ₀ y ≤ ⊤)
  · exact cramerRateFunction_le_cramerRateFromSanov_of_HasFiniteMGF μ₀ y hMGF (hbdd y)

/-! ### Wiring notes toward `cramer_theorem`

Intended statement (Def-shaped: i.i.d. / product empirical means under vector hMGF):

```
theorem cramer_theorem {d} (μ₀ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ₀] (hMGF : HasFiniteMGF μ₀)
    (hcover : TiltCover μ₀ hMGF) ... :
    SatisfiesLDP (fun n => empiricalMeanLawPi μ₀ n)
      (cramerRateFunction (fun x => x) μ₀)
```

Path: Sanov `Random.SatisfiesLDP` → contract by barycenter (via
`satisfiesLDP_map_of_continuous_of_measurable` on truncated means, or
`UniformExpMoment` + seq contraction after exponential tightness) → identify contracted
KL rate with `cramerRateFunction` by `cramerRateFromSanov_eq_cramerRateFunction_of_tiltCover`
→ transport along `empiricalMeanLawPi_eq_map_barycenter_comp` /
`empiricalMeanMeasureVec_eq_empiricalMeanLawPi`.

Blocked without sorry: (1) Continuous/Measurable barycenter on the Sanov support
(exponential tightness into `UniformExpMoment`, or R→∞ truncation limit for LDP);
(2) proof of `TiltCover` under hMGF (convex analysis).
-/


/-! ### Tilt means as Legendre maximizers; helper `cramer_theorem` -/

/-- Barycenter of an exponentially tilted law as a Bochner integral under `μ₀`. -/
theorem barycenter_tiltedProba_eq {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (t : EuclideanSpace ℝ (Fin d))
    (hf : Integrable (fun x => Real.exp (⟪t, x⟫_ℝ)) μ₀)
    (hint_id : Integrable (fun x : EuclideanSpace ℝ (Fin d) => x)
      (μ₀.tilted fun x => ⟪t, x⟫_ℝ)) :
    barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) hf) =
      ∫ x, (Real.exp (⟪t, x⟫_ℝ) / ∫ y, Real.exp (⟪t, y⟫_ℝ) ∂μ₀) • x ∂μ₀ := by
  simpa [barycenter, tiltedProba] using
    (integral_tilted (fun x => ⟪t, x⟫_ℝ)
      (fun x : EuclideanSpace ℝ (Fin d) => x) (μ := μ₀))

/-- At a tilt barycenter, every Fenchel–Young competitor sits below the tilt value
(Donsker–Varadhan applied to the tilt, with `HasFiniteMGF` discharging dominates). -/
theorem fy_le_fy_of_tilted_of_HasFiniteMGF {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (t s : EuclideanSpace ℝ (Fin d))
    (hMGF : HasFiniteMGF μ₀) :
    ⟪s, barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))⟫_ℝ -
        logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ s ≤
      ⟪t, barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))⟫_ℝ -
        logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t := by
  haveI : IsProbabilityMeasure (μ₀.tilted fun x => ⟪t, x⟫_ℝ) :=
    isProbabilityMeasure_tilted (hMGF t)
  have htiltMGF := hMGF.tilted t
  have hint_id := htiltMGF.integrable_id
  have hf_inner : Integrable (fun x => ⟪t, x⟫_ℝ) (μ₀.tilted fun x => ⟪t, x⟫_ℝ) :=
    (innerSL ℝ t).integrable_comp hint_id
  set ν := tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t)
  have hac : ν.toMeasure ≪ μ₀ := by
    simpa [ν, tiltedProba] using tilted_absolutelyContinuous μ₀ (fun x => ⟪t, x⟫_ℝ)
  have hllr_ae : llr ν.toMeasure μ₀ =ᵐ[ν.toMeasure]
      fun x => ⟪t, x⟫_ℝ - Real.log (∫ z, Real.exp (⟪t, z⟫_ℝ) ∂μ₀) := by
    change llr (μ₀.tilted fun x => ⟪t, x⟫_ℝ) μ₀ =ᵐ[μ₀.tilted fun x => ⟪t, x⟫_ℝ] _
    exact (tilted_absolutelyContinuous μ₀ (fun x => ⟪t, x⟫_ℝ)).ae_le
      (log_rnDeriv_tilted_left_self (hMGF t))
  have hllr_int : Integrable (llr ν.toMeasure μ₀) ν.toMeasure :=
    (integrable_congr hllr_ae).mpr (hf_inner.sub (integrable_const _))
  have hDV := ofReal_inner_barycenter_sub_log_le_klDiv_of_expNorm μ₀ ν s hac hllr_int hint_id
    (hMGF s) (hMGF.integrable_exp_mul_norm ‖s‖)
  have hkl := toReal_klDiv_tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t) hf_inner
  have hne : klDiv ν.toMeasure μ₀ ≠ ⊤ := klDiv_ne_top hac hllr_int
  have hfy_s :
      ⟪s, barycenter ν⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ s ≤
        (klDiv ν.toMeasure μ₀).toReal := by
    have := (ENNReal.ofReal_le_iff_le_toReal hne).mp (by
      simpa [logMGFVec_id, ν] using hDV)
    simpa [logMGFVec_id] using this
  have hfy_t :
      (klDiv ν.toMeasure μ₀).toReal =
        ⟪t, barycenter ν⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t := by
    have hinner := integral_inner_eq_inner_barycenter ν t hint_id
    calc (klDiv ν.toMeasure μ₀).toReal
        = (∫ x, ⟪t, x⟫_ℝ ∂ν.toMeasure) -
            Real.log (∫ z, Real.exp (⟪t, z⟫_ℝ) ∂μ₀) := by
              simpa [ν, tiltedProba] using hkl
      _ = ⟪t, barycenter ν⟫_ℝ -
            logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t := by
              simp [logMGFVec_id, hinner]
  exact hfy_s.trans_eq hfy_t

/-- Legendre transform equals the tilt Fenchel–Young value at every tilt barycenter. -/
theorem legendreTransform_eq_fy_of_tilted_of_HasFiniteMGF {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (t : EuclideanSpace ℝ (Fin d))
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : BddAbove (Set.range fun s : EuclideanSpace ℝ (Fin d) =>
      ⟪s, barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))⟫_ℝ -
        logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ s)) :
    legendreTransform (logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀)
        (barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))) =
      ⟪t, barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))⟫_ℝ -
        logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t := by
  apply le_antisymm
  · refine ciSup_le fun s =>
      fy_le_fy_of_tilted_of_HasFiniteMGF μ₀ t s hMGF
  · exact le_legendreTransform _ _ t hbdd

/-- Tilt barycenters have finite Cramér rate (equal to the tilt KL). -/
theorem cramerRateFunction_ne_top_of_tilted_of_HasFiniteMGF {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (t : EuclideanSpace ℝ (Fin d))
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : BddAbove (Set.range fun s : EuclideanSpace ℝ (Fin d) =>
      ⟪s, barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))⟫_ℝ -
        logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ s)) :
    cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀
        (barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))) ≠ ∞ := by
  have heq := legendreTransform_eq_fy_of_tilted_of_HasFiniteMGF μ₀ t hMGF hbdd
  unfold cramerRateFunction
  rw [heq]
  exact ENNReal.ofReal_ne_top

/-- Transfer `SatisfiesLDP` along a pointwise-equal rate (new rate must be lsc). -/
theorem SatisfiesLDP.congr_rate {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : ℕ → Measure X} {I J : X → ENNReal}
    (h : SatisfiesLDP μ I) (hIJ : ∀ x, I x = J x)
    (hJ : LowerSemicontinuous J) :
    SatisfiesLDP μ J := by
  refine ⟨⟨hJ⟩, ?_, ?_⟩
  · intro U hU
    have hinf : (⨅ x ∈ U, (I x : EReal)) = ⨅ x ∈ U, (J x : EReal) := by
      refine iInf_congr fun x => iInf_congr fun _ => ?_
      simp [hIJ x]
    simpa [hinf] using h.lower_bound U hU
  · intro F hF
    have hinf : (⨅ x ∈ F, (I x : EReal)) = ⨅ x ∈ F, (J x : EReal) := by
      refine iInf_congr fun x => iInf_congr fun _ => ?_
      simp [hIJ x]
    simpa [hinf] using h.upper_bound F hF

/-- Helper **Cramér theorem** (Def-shaped empirical-mean laws; rate = `cramerRateFunction`).

Assumes Sanov has already been contracted to `cramerRateFromSanov` on
`empiricalMeanLawPi` (gap: Giry-safe barycenter / UniformExpMoment exp-tightness /
truncation limit), and `TiltCover` (gap: surjectivity of ∇Λ under essential smoothness).
Under those residual hyps the rate identification of `CramerRateID` finishes the proof. -/
theorem cramer_theorem {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hcover : TiltCover μ₀ hMGF)
    (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t))
    (hid : ∀ y : EuclideanSpace ℝ (Fin d),
      ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
        barycenter ν = y → Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.toMeasure)
    (hLDP : SatisfiesLDP (fun n => empiricalMeanLawPi μ₀ n) (cramerRateFromSanov μ₀))
    (hRate : LowerSemicontinuous
      (cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀)) :
    SatisfiesLDP (fun n => empiricalMeanLawPi μ₀ n)
      (cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀) := by
  have heq := cramerRateFromSanov_eq_cramerRateFunction_of_tiltCover
    μ₀ hMGF hcover hbdd hid
  exact hLDP.congr_rate heq hRate

/-! ### Residual discharge: local `hbdd` / tilt `hid`, primed rate IDs -/

/-- At a tilt barycenter the Fenchel–Young integrand is bounded above by its tilt value
(so the real Legendre `ciSup` is a true supremum). Discharges the local `hbdd` residual. -/
theorem bddAbove_fy_of_tilted_of_HasFiniteMGF {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (t : EuclideanSpace ℝ (Fin d))
    (hMGF : HasFiniteMGF μ₀) :
    BddAbove (Set.range fun s : EuclideanSpace ℝ (Fin d) =>
      ⟪s, barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))⟫_ℝ -
        logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ s) := by
  refine ⟨⟪t, barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))⟫_ℝ -
      logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t, ?_⟩
  rintro _ ⟨s, rfl⟩
  exact fy_le_fy_of_tilted_of_HasFiniteMGF μ₀ t s hMGF

/-- Fiberwise first-moment hyp on the tilt itself (the tilt measure is always integrable). -/
theorem integrable_id_tiltedProba_of_HasFiniteMGF {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (t : EuclideanSpace ℝ (Fin d))
    (hMGF : HasFiniteMGF μ₀) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => x)
      (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t)).toMeasure := by
  have : IsProbabilityMeasure (μ₀.tilted fun x => ⟪t, x⟫_ℝ) :=
    isProbabilityMeasure_tilted (hMGF t)
  simpa [tiltedProba] using (hMGF.tilted t).integrable_id

/-- Rate equality at tilt means with local `hbdd` discharged from `HasFiniteMGF`. -/
theorem cramerRateFromSanov_eq_cramerRateFunction_of_tilted_of_HasFiniteMGF' {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (t : EuclideanSpace ℝ (Fin d))
    (hMGF : HasFiniteMGF μ₀)
    (hid : ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      barycenter ν = barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t)) →
        Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.toMeasure) :
    cramerRateFromSanov μ₀ (barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))) =
      cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀
        (barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))) :=
  cramerRateFromSanov_eq_cramerRateFunction_of_tilted_of_HasFiniteMGF μ₀ t hMGF
    (bddAbove_fy_of_tilted_of_HasFiniteMGF μ₀ t hMGF) hid

/-- Legendre = tilt FY value with local `hbdd` discharged. -/
theorem legendreTransform_eq_fy_of_tilted_of_HasFiniteMGF' {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (t : EuclideanSpace ℝ (Fin d))
    (hMGF : HasFiniteMGF μ₀) :
    legendreTransform (logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀)
      (barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))) =
      ⟪t, barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))⟫_ℝ -
        logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t :=
  legendreTransform_eq_fy_of_tilted_of_HasFiniteMGF μ₀ t hMGF
    (bddAbove_fy_of_tilted_of_HasFiniteMGF μ₀ t hMGF)

/-- Finite Cramér rate at tilt means with local `hbdd` discharged. -/
theorem cramerRateFunction_ne_top_of_tilted_of_HasFiniteMGF' {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (t : EuclideanSpace ℝ (Fin d))
    (hMGF : HasFiniteMGF μ₀) :
    cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀
        (barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))) ≠ ∞ :=
  cramerRateFunction_ne_top_of_tilted_of_HasFiniteMGF μ₀ t hMGF
    (bddAbove_fy_of_tilted_of_HasFiniteMGF μ₀ t hMGF)

/-! ### Raywise cumulant derivative = tilt mean (Mathlib 1D `integral_tilted_mul_self`) -/

/-- Under vector hMGF every dual ray has full exponential-moment interval. -/
theorem integrableExpSet_inner_eq_univ_of_HasFiniteMGF {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀) (u : EuclideanSpace ℝ (Fin d)) :
    integrableExpSet (fun x : EuclideanSpace ℝ (Fin d) => ⟪u, x⟫_ℝ) μ₀ = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  refine (hMGF (t • u)).congr (Eventually.of_forall fun x => ?_)
  simp [smul_eq_mul, real_inner_smul_left, mul_comm]

/-- Vector CGF along a ray equals the scalar `cgf` of the linear form. -/
theorem logMGFVec_smul_eq_cgf_inner {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (u : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ (t • u) =
      ProbabilityTheory.cgf (fun x : EuclideanSpace ℝ (Fin d) => ⟪u, x⟫_ℝ) μ₀ t := by
  simp [logMGFVec, ProbabilityTheory.cgf, ProbabilityTheory.mgf, real_inner_smul_left, mul_comm]

/-- Directional derivative of `logMGFVec` along `u` equals the tilt mean of `⟪u,·⟫`.
Uses Mathlib's 1D identity `integral_tilted_mul_self` under vector hMGF (full moment interval). -/
theorem inner_barycenter_tilted_eq_deriv_cgf_of_HasFiniteMGF {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀) (u : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    ⟪u, barycenter (tiltedProba μ₀ (fun x => ⟪(t • u), x⟫_ℝ) (hMGF (t • u)))⟫_ℝ =
      deriv (ProbabilityTheory.cgf (fun x : EuclideanSpace ℝ (Fin d) => ⟪u, x⟫_ℝ) μ₀) t := by
  have huniv := integrableExpSet_inner_eq_univ_of_HasFiniteMGF μ₀ hMGF u
  have hint : t ∈ interior (integrableExpSet (fun x : EuclideanSpace ℝ (Fin d) => ⟪u, x⟫_ℝ) μ₀) := by
    simp [huniv]
  have hmath :=
    ProbabilityTheory.integral_tilted_mul_self
      (X := fun x : EuclideanSpace ℝ (Fin d) => ⟪u, x⟫_ℝ) (μ := μ₀) hint
  have hint_id := integrable_id_tiltedProba_of_HasFiniteMGF μ₀ (t • u) hMGF
  have hinner :=
    integral_inner_eq_inner_barycenter
      (tiltedProba μ₀ (fun x => ⟪(t • u), x⟫_ℝ) (hMGF (t • u))) u hint_id
  -- Mathlib tilts by `t * X`; we tilt by `⟪t•u, ·⟫ = t * ⟪u,·⟫`.
  have htilt_eq :
      (μ₀.tilted fun x => t * ⟪u, x⟫_ℝ) =
        (tiltedProba μ₀ (fun x => ⟪(t • u), x⟫_ℝ) (hMGF (t • u))).toMeasure := by
    simp [tiltedProba, real_inner_smul_left, mul_comm]
  calc ⟪u, barycenter (tiltedProba μ₀ (fun x => ⟪(t • u), x⟫_ℝ) (hMGF (t • u)))⟫_ℝ
      = ∫ x, ⟪u, x⟫_ℝ ∂(tiltedProba μ₀ (fun x => ⟪(t • u), x⟫_ℝ) (hMGF (t • u))).toMeasure :=
        hinner.symm
    _ = ∫ x, ⟪u, x⟫_ℝ ∂(μ₀.tilted fun x => t * ⟪u, x⟫_ℝ) := by rw [← htilt_eq]
    _ = deriv (ProbabilityTheory.cgf (fun x : EuclideanSpace ℝ (Fin d) => ⟪u, x⟫_ℝ) μ₀) t := hmath

/-- Same identity rewritten with `logMGFVec` along the ray. -/
theorem inner_barycenter_tilted_eq_deriv_logMGFVec_ray_of_HasFiniteMGF {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀) (u : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    ⟪u, barycenter (tiltedProba μ₀ (fun x => ⟪(t • u), x⟫_ℝ) (hMGF (t • u)))⟫_ℝ =
      deriv (fun s : ℝ => logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ (s • u)) t := by
  have h := inner_barycenter_tilted_eq_deriv_cgf_of_HasFiniteMGF μ₀ hMGF u t
  rw [h]
  refine (congrArg (fun f : ℝ → ℝ => deriv f t)
    (funext fun s => logMGFVec_smul_eq_cgf_inner μ₀ u s)).symm

/-- Under `TiltCover`, every finite-Cramér-rate point inherits local `hbdd` from its tilt
representative. Global `hbdd` on `{CRF = ∞}` remains open (and Defs `ciSup` is unreliable there). -/
theorem bddAbove_fy_of_tiltCover_of_cramerRateFunction_lt_top {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀) (hcover : TiltCover μ₀ hMGF)
    (y : EuclideanSpace ℝ (Fin d))
    (hy : cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y < ∞) :
    BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
      ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t) := by
  obtain ⟨t, ht⟩ := hcover y hy
  simpa [ht] using bddAbove_fy_of_tilted_of_HasFiniteMGF μ₀ t hMGF


/-! ### Continuous CGF, directional derivative, maximizer ⇒ TiltCover -/

/-- Local domination: near `t₀`, `exp⟨t,x⟩ ≤ exp((‖t₀‖+R)‖x‖)`. -/
theorem exp_inner_le_exp_mul_norm_of_mem_closedBall {d : ℕ}
    (t₀ : EuclideanSpace ℝ (Fin d)) {R : ℝ} (hR : 0 ≤ R)
    {t : EuclideanSpace ℝ (Fin d)} (ht : ‖t - t₀‖ ≤ R)
    (x : EuclideanSpace ℝ (Fin d)) :
    Real.exp (⟪t, x⟫_ℝ) ≤ Real.exp ((‖t₀‖ + R) * ‖x‖) := by
  have h1 : ⟪t, x⟫_ℝ ≤ ‖t‖ * ‖x‖ := real_inner_le_norm _ _
  have h2 : ‖t‖ ≤ ‖t₀‖ + R :=
    (norm_le_norm_add_norm_sub' t t₀).trans (add_le_add le_rfl ht)
  exact Real.exp_le_exp.mpr (h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)))

/-- Vector MGF `t ↦ ∫ exp⟨t,x⟩` is continuous under `HasFiniteMGF`. -/
theorem continuous_integral_exp_inner_of_HasFiniteMGF {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀) :
    Continuous fun t : EuclideanSpace ℝ (Fin d) => ∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀ := by
  refine continuous_iff_continuousAt.mpr fun t₀ => ?_
  let R : ℝ := 1
  have hR0 : 0 ≤ R := zero_le_one
  have hRpos : 0 < R := one_pos
  let bound : EuclideanSpace ℝ (Fin d) → ℝ := fun x => Real.exp ((‖t₀‖ + R) * ‖x‖)
  have hbound_int : Integrable bound μ₀ := by
    simpa [bound] using hMGF.integrable_exp_mul_norm (‖t₀‖ + R)
  refine MeasureTheory.continuousAt_of_dominated
    (F := fun t x => Real.exp (⟪t, x⟫_ℝ)) (μ := μ₀) (bound := bound) ?_ ?_ hbound_int ?_
  · exact Eventually.of_forall fun t =>
      (Real.continuous_exp.comp
        ((continuous_const : Continuous fun _ : EuclideanSpace ℝ (Fin d) => t).inner
          continuous_id)).aestronglyMeasurable
  · refine Metric.eventually_nhds_iff.mpr ⟨R, hRpos, fun t ht => ?_⟩
    have ht' : ‖t - t₀‖ ≤ R := le_of_lt ht
    exact Eventually.of_forall fun x => by
      have := exp_inner_le_exp_mul_norm_of_mem_closedBall t₀ hR0 ht' x
      simpa [bound, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using this
  · exact Eventually.of_forall fun x =>
      (Real.continuous_exp.comp
        (continuous_id.inner (continuous_const : Continuous fun _ => x))).continuousAt

/-- Strict positivity of the vector MGF under hMGF. -/
theorem integral_exp_inner_pos_of_HasFiniteMGF {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀) (t : EuclideanSpace ℝ (Fin d)) :
    0 < ∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀ := by
  have hint : Integrable (fun x => Real.exp (1 * ⟪t, x⟫_ℝ)) μ₀ := by
    refine (hMGF t).congr (Eventually.of_forall fun x => ?_)
    simp [mul_comm]
  simpa [mgf] using
    (mgf_pos (X := fun x : EuclideanSpace ℝ (Fin d) => ⟪t, x⟫_ℝ) (μ := μ₀) hint)

/-- `logMGFVec` on the identity sample is continuous under vector hMGF. -/
theorem continuous_logMGFVec_id_of_HasFiniteMGF {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀) :
    Continuous (logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀) := by
  have hint := continuous_integral_exp_inner_of_HasFiniteMGF μ₀ hMGF
  have hpos := integral_exp_inner_pos_of_HasFiniteMGF μ₀ hMGF
  have heq : logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ =
      fun t => Real.log (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀) := by
    ext t; rfl
  rw [heq]
  exact Real.continuousOn_log.comp_continuous hint fun t => (hpos t).ne'

/-- FY integrand is continuous under hMGF. -/
theorem continuous_fy_of_HasFiniteMGF {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀) (y : EuclideanSpace ℝ (Fin d)) :
    Continuous fun t : EuclideanSpace ℝ (Fin d) =>
      ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t :=
  (continuous_id.inner continuous_const).sub
    (continuous_logMGFVec_id_of_HasFiniteMGF μ₀ hMGF)

/-- Λ(t + ε•u) = Λ(t) + cgf_{tilt t}(⟨u,·⟩)(ε). -/
theorem logMGFVec_add_smul_eq_add_cgf_tilted {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (t u : EuclideanSpace ℝ (Fin d)) (ε : ℝ) :
    logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ (t + ε • u) =
      logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t +
        cgf (fun x : EuclideanSpace ℝ (Fin d) => ⟪u, x⟫_ℝ)
          (μ₀.tilted fun x => ⟪t, x⟫_ℝ) ε := by
  haveI : IsProbabilityMeasure (μ₀.tilted fun x => ⟪t, x⟫_ℝ) :=
    isProbabilityMeasure_tilted (hMGF t)
  have h := integral_exp_tilted (μ := μ₀) (f := fun x => ⟪t, x⟫_ℝ)
    (g := fun x => ε * ⟪u, x⟫_ℝ)
  have hmgf :
      mgf (fun x : EuclideanSpace ℝ (Fin d) => ⟪u, x⟫_ℝ)
          (μ₀.tilted fun x => ⟪t, x⟫_ℝ) ε =
        (∫ x, Real.exp (⟪t + ε • u, x⟫_ℝ) ∂μ₀) /
          (∫ x, Real.exp (⟪t, x⟫_ℝ) ∂μ₀) := by
    simp only [mgf]
    refine h.trans ?_
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    congr 1
    simp [inner_add_left, inner_smul_left, real_inner_smul_left, mul_comm ε]
  have hZ := integral_exp_inner_pos_of_HasFiniteMGF μ₀ hMGF t
  have hZ' := integral_exp_inner_pos_of_HasFiniteMGF μ₀ hMGF (t + ε • u)
  simp only [logMGFVec, cgf, hmgf]
  rw [Real.log_div hZ'.ne' hZ.ne']
  abel

/-- Directional derivative of Λ at `t` along `u` equals `⟨u, bary(tilt t)⟩`. -/
theorem hasDerivAt_logMGFVec_add_smul_of_HasFiniteMGF {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (t u : EuclideanSpace ℝ (Fin d)) :
    HasDerivAt
      (fun ε : ℝ => logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ (t + ε • u))
      (⟪u, barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))⟫_ℝ) 0 := by
  haveI : IsProbabilityMeasure (μ₀.tilted fun x => ⟪t, x⟫_ℝ) :=
    isProbabilityMeasure_tilted (hMGF t)
  have htiltMGF := hMGF.tilted t
  have huniv := integrableExpSet_inner_eq_univ_of_HasFiniteMGF
    (μ₀.tilted fun x => ⟪t, x⟫_ℝ) htiltMGF u
  have hint : (0 : ℝ) ∈
      interior (integrableExpSet (fun x : EuclideanSpace ℝ (Fin d) => ⟪u, x⟫_ℝ)
        (μ₀.tilted fun x => ⟪t, x⟫_ℝ)) := by simp [huniv]
  have hderiv0 :
      deriv (cgf (fun x : EuclideanSpace ℝ (Fin d) => ⟪u, x⟫_ℝ)
        (μ₀.tilted fun x => ⟪t, x⟫_ℝ)) 0 =
        ∫ x, ⟪u, x⟫_ℝ ∂(μ₀.tilted fun x => ⟪t, x⟫_ℝ) := by
    have h := integral_tilted_mul_self
      (X := fun x : EuclideanSpace ℝ (Fin d) => ⟪u, x⟫_ℝ)
      (μ := μ₀.tilted fun x => ⟪t, x⟫_ℝ) hint
    have htilt0 :
        ((μ₀.tilted fun x => ⟪t, x⟫_ℝ).tilted fun x => (0 : ℝ) * ⟪u, x⟫_ℝ) =
          μ₀.tilted fun x => ⟪t, x⟫_ℝ := by
      simpa using tilted_zero (μ₀.tilted fun x => ⟪t, x⟫_ℝ)
    simpa [htilt0] using h.symm
  have hfun :
      (fun ε : ℝ => logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ (t + ε • u)) =
        fun ε => logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t +
          cgf (fun x : EuclideanSpace ℝ (Fin d) => ⟪u, x⟫_ℝ)
            (μ₀.tilted fun x => ⟪t, x⟫_ℝ) ε :=
    funext fun ε => logMGFVec_add_smul_eq_add_cgf_tilted μ₀ hMGF t u ε
  have hcgfAt := (analyticAt_cgf hint).differentiableAt.hasDerivAt
  have hint_id := integrable_id_tiltedProba_of_HasFiniteMGF μ₀ t hMGF
  have hinner :=
    integral_inner_eq_inner_barycenter
      (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t)) u hint_id
  have hder : ⟪u, barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))⟫_ℝ =
      deriv (cgf (fun x : EuclideanSpace ℝ (Fin d) => ⟪u, x⟫_ℝ)
        (μ₀.tilted fun x => ⟪t, x⟫_ℝ)) 0 := by
    rw [hderiv0, ← hinner]
    simp [tiltedProba]
  have hconst :
      HasDerivAt
        (fun ε : ℝ =>
          logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t +
            cgf (fun x : EuclideanSpace ℝ (Fin d) => ⟪u, x⟫_ℝ)
              (μ₀.tilted fun x => ⟪t, x⟫_ℝ) ε)
        (deriv (cgf (fun x : EuclideanSpace ℝ (Fin d) => ⟪u, x⟫_ℝ)
          (μ₀.tilted fun x => ⟪t, x⟫_ℝ)) 0) 0 :=
    hcgfAt.const_add _
  simpa [hfun, hder] using hconst

/-- A global FY maximizer is a tilt representing `y`. -/
theorem eq_barycenter_tilted_of_isMaxOn_fy {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (y t : EuclideanSpace ℝ (Fin d))
    (hmax : IsMaxOn
      (fun s : EuclideanSpace ℝ (Fin d) =>
        ⟪s, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ s)
      Set.univ t) :
    barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t)) = y := by
  refine ext_inner_left ℝ fun u => ?_
  let φ : ℝ → ℝ := fun ε =>
    ⟪t + ε • u, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ (t + ε • u)
  have hmax1d : IsMaxOn φ Set.univ 0 := by
    intro ε _
    have h := hmax (Set.mem_univ (t + ε • u))
    -- h : ⟨t+εu,y⟩ - Λ(t+εu) ≤ ⟨t,y⟩ - Λ(t)
    change φ ε ≤ φ 0
    simpa [φ, inner_add_left, inner_smul_left, mul_comm] using h
  have hφmax : IsLocalMax φ 0 :=
    hmax1d.isLocalMax (isOpen_univ.mem_nhds (Set.mem_univ 0))
  have hlin : (fun ε : ℝ => ⟪t + ε • u, y⟫_ℝ) = fun ε => ⟪t, y⟫_ℝ + ⟪u, y⟫_ℝ * ε := by
    ext ε; simp [inner_add_left, inner_smul_left, mul_comm]
  have hR : HasDerivAt (fun ε : ℝ => ⟪t + ε • u, y⟫_ℝ) (⟪u, y⟫_ℝ) 0 := by
    rw [hlin]
    simpa using (((hasDerivAt_id (0 : ℝ)).const_mul (⟪u, y⟫_ℝ)).const_add (⟪t, y⟫_ℝ))
  have hL := hasDerivAt_logMGFVec_add_smul_of_HasFiniteMGF μ₀ hMGF t u
  have hderivφ : HasDerivAt φ
      (⟪u, y⟫_ℝ - ⟪u, barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t))⟫_ℝ) 0 :=
    hR.sub hL
  have h0 : deriv φ 0 = 0 := hφmax.deriv_eq_zero
  have hval := hderivφ.deriv
  linarith [h0, hval]

/-- Existence of FY maximizers on the finite-rate set ⇒ `TiltCover`. -/
theorem TiltCover_of_exists_isMaxOn_fy {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hmax : ∀ y : EuclideanSpace ℝ (Fin d),
      cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y < ∞ →
        ∃ t : EuclideanSpace ℝ (Fin d),
          IsMaxOn
            (fun s : EuclideanSpace ℝ (Fin d) =>
              ⟪s, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ s)
            Set.univ t) :
    TiltCover μ₀ hMGF := by
  intro y hy
  obtain ⟨t, ht⟩ := hmax y hy
  exact ⟨t, eq_barycenter_tilted_of_isMaxOn_fy μ₀ hMGF y t ht⟩

/-- Cocompact coercivity of FY ⇒ maximizers ⇒ `TiltCover`. -/
theorem TiltCover_of_fy_tendsto_cocompact_atBot {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hcoer : ∀ y : EuclideanSpace ℝ (Fin d),
      cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y < ∞ →
        Tendsto
          (fun t : EuclideanSpace ℝ (Fin d) =>
            ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t)
          (cocompact (EuclideanSpace ℝ (Fin d))) atBot) :
    TiltCover μ₀ hMGF := by
  refine TiltCover_of_exists_isMaxOn_fy μ₀ hMGF fun y hy => ?_
  have hcont := continuous_fy_of_HasFiniteMGF μ₀ hMGF y
  obtain ⟨t, ht⟩ := hcont.exists_forall_ge (hcoer y hy)
  exact ⟨t, fun s _ => ht s⟩

/-- If FY is unbounded above then the contracted Sanov rate is `∞` (DV + fiber `hid`). -/
theorem cramerRateFromSanov_eq_top_of_not_bddAbove {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (y : EuclideanSpace ℝ (Fin d))
    (hid : ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      barycenter ν = y → Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.toMeasure)
    (hnbdd : ¬ BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
      ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t)) :
    cramerRateFromSanov μ₀ y = ∞ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := not_bddAbove_iff'.mp hnbdd (r : ℝ)
  have hlt : (r : ℝ) <
      ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t :=
    lt_of_not_ge ht
  have hle :=
    ofReal_inner_sub_log_le_cramerRateFromSanov_of_expNorm_of_integrableId
      μ₀ y t (hMGF t) (hMGF.integrable_exp_mul_norm ‖t‖) hid
  have hr : (r : ENNReal) = ENNReal.ofReal (r : ℝ) := by simp
  rw [hr]
  refine (ENNReal.ofReal_le_ofReal hlt.le).trans ?_
  simpa [logMGFVec_id] using hle


/-! ### Fenchel–Young equality characterization and coercivity wrapper -/

/-- Attaining the Legendre value at `t` is an FY maximizer. -/
theorem isMaxOn_fy_of_legendreTransform_eq {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (y t : EuclideanSpace ℝ (Fin d))
    (hbdd : BddAbove (Set.range fun s : EuclideanSpace ℝ (Fin d) =>
      ⟪s, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ s))
    (heq : legendreTransform (logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀) y =
      ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t) :
    IsMaxOn
      (fun s : EuclideanSpace ℝ (Fin d) =>
        ⟪s, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ s)
      Set.univ t := by
  intro s _
  have hs := le_legendreTransform
    (logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀) y s hbdd
  exact hs.trans_eq heq

/-- FY equality at `t` ⇒ `y` is the tilt barycenter of `t` (path (c)). -/
theorem eq_barycenter_tilted_of_legendreTransform_eq_fy {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (y t : EuclideanSpace ℝ (Fin d))
    (hbdd : BddAbove (Set.range fun s : EuclideanSpace ℝ (Fin d) =>
      ⟪s, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ s))
    (heq : legendreTransform (logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀) y =
      ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t) :
    barycenter (tiltedProba μ₀ (fun x => ⟪t, x⟫_ℝ) (hMGF t)) = y :=
  eq_barycenter_tilted_of_isMaxOn_fy μ₀ hMGF y t
    (isMaxOn_fy_of_legendreTransform_eq μ₀ y t hbdd heq)

/-- Existence of FY-equality representatives on `{CRF < ∞}` ⇒ `TiltCover`. -/
theorem TiltCover_of_exists_legendreTransform_eq_fy {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun s : EuclideanSpace ℝ (Fin d) =>
        ⟪s, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ s))
    (hrep : ∀ y : EuclideanSpace ℝ (Fin d),
      cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y < ∞ →
        ∃ t : EuclideanSpace ℝ (Fin d),
          legendreTransform (logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀) y =
            ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t) :
    TiltCover μ₀ hMGF := by
  intro y hy
  obtain ⟨t, ht⟩ := hrep y hy
  exact ⟨t, eq_barycenter_tilted_of_legendreTransform_eq_fy μ₀ hMGF y t (hbdd y) ht⟩

/-- Helper Cramér theorem with `TiltCover` discharged by FY cocompact coercivity.
Still needs Sanov contraction `hLDP`, global `hbdd`/`hid`, and CRF lsc. -/
theorem cramer_theorem_of_fy_tendsto_cocompact {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hcoer : ∀ y : EuclideanSpace ℝ (Fin d),
      cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y < ∞ →
        Tendsto
          (fun t : EuclideanSpace ℝ (Fin d) =>
            ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t)
          (cocompact (EuclideanSpace ℝ (Fin d))) atBot)
    (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t))
    (hid : ∀ y : EuclideanSpace ℝ (Fin d),
      ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
        barycenter ν = y → Integrable (fun x : EuclideanSpace ℝ (Fin d) => x) ν.toMeasure)
    (hLDP : SatisfiesLDP (fun n => empiricalMeanLawPi μ₀ n) (cramerRateFromSanov μ₀))
    (hRate : LowerSemicontinuous
      (cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀)) :
    SatisfiesLDP (fun n => empiricalMeanLawPi μ₀ n)
      (cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀) :=
  cramer_theorem μ₀ hMGF
    (TiltCover_of_fy_tendsto_cocompact_atBot μ₀ hMGF hcoer) hbdd hid hLDP hRate


/-! ### Global lsc of Legendre / CRF under continuous Λ + pointwise `hbdd` -/

/-- Real Legendre transform of a continuous `Λ` is lsc wherever the FY range is pointwise bounded above. -/
theorem lowerSemicontinuous_legendreTransform_of_continuous {d : ℕ}
    (Λ : EuclideanSpace ℝ (Fin d) → ℝ) (hΛ : Continuous Λ)
    (hbdd : ∀ x : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun l : EuclideanSpace ℝ (Fin d) => ⟪l, x⟫_ℝ - Λ l)) :
    LowerSemicontinuous (legendreTransform Λ) := by
  refine lowerSemicontinuous_ciSup hbdd fun l => ?_
  exact (((innerSL ℝ l).continuous.sub continuous_const).lowerSemicontinuous)

/-- Under vector hMGF and global `hbdd`, the Def Cramér rate is lower semicontinuous. -/
theorem lowerSemicontinuous_cramerRateFunction_of_HasFiniteMGF {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t)) :
    LowerSemicontinuous
      (cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀) := by
  have hΛ := continuous_logMGFVec_id_of_HasFiniteMGF μ₀ hMGF
  have hl := lowerSemicontinuous_legendreTransform_of_continuous
    (logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀) hΛ hbdd
  exact ENNReal.continuous_ofReal.comp_lowerSemicontinuous hl ENNReal.ofReal_mono


/-! ### FY cocompact coercivity from global `hbdd` (finite Λ* everywhere) -/

/-- Under pointwise `hbdd`, the real Legendre transform is convex on all of `ℝᵈ`. -/
theorem convexOn_legendreTransform_of_forall_bddAbove {d : ℕ}
    (Λ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hbdd : ∀ x : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun l : EuclideanSpace ℝ (Fin d) => ⟪l, x⟫_ℝ - Λ l)) :
    ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin d))) (legendreTransform Λ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _hx y _hy a b ha hb hab
  exact convex_legendreTransform Λ ha hb hab (hbdd x) (hbdd y) (hbdd _)

/-- Continuous Legendre under global `hbdd` (finite-dimensional convex ⇒ continuous). -/
theorem continuous_legendreTransform_of_forall_bddAbove {d : ℕ}
    (Λ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hbdd : ∀ x : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun l : EuclideanSpace ℝ (Fin d) => ⟪l, x⟫_ℝ - Λ l)) :
    Continuous (legendreTransform Λ) := by
  have hconvex := convexOn_legendreTransform_of_forall_bddAbove Λ hbdd
  exact continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hconvex)

/-- Uniform bound of Λ* on a closed ball, from global `hbdd`. -/
theorem exists_ball_bound_legendreTransform_of_forall_bddAbove {d : ℕ}
    (Λ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hbdd : ∀ x : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun l : EuclideanSpace ℝ (Fin d) => ⟪l, x⟫_ℝ - Λ l))
    (y : EuclideanSpace ℝ (Fin d)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, ∀ z : EuclideanSpace ℝ (Fin d), ‖z - y‖ ≤ δ →
      legendreTransform Λ z ≤ M := by
  have hcont := continuous_legendreTransform_of_forall_bddAbove Λ hbdd
  let K : Set (EuclideanSpace ℝ (Fin d)) := Metric.closedBall y δ
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨z0, hz0K, hmax⟩ :=
    hK.exists_isMaxOn (Metric.nonempty_closedBall.2 hδ.le) hcont.continuousOn
  refine ⟨legendreTransform Λ z0, fun z hz => ?_⟩
  exact hmax (Metric.mem_closedBall.mpr hz)

/-- Interior-ball recession: `fy(t) ≤ M - δ ‖t‖`. -/
theorem fy_le_sub_mul_norm_of_ball_bound {d : ℕ}
    (Λ : EuclideanSpace ℝ (Fin d) → ℝ) (y : EuclideanSpace ℝ (Fin d))
    {δ M : ℝ} (hδ : 0 < δ)
    (hbdd : ∀ x : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun l : EuclideanSpace ℝ (Fin d) => ⟪l, x⟫_ℝ - Λ l))
    (hM : ∀ z : EuclideanSpace ℝ (Fin d), ‖z - y‖ ≤ δ → legendreTransform Λ z ≤ M)
    (t : EuclideanSpace ℝ (Fin d)) :
    ⟪t, y⟫_ℝ - Λ t ≤ M - δ * ‖t‖ := by
  by_cases ht : t = 0
  · subst ht
    have hy0 := le_legendreTransform Λ y 0 (hbdd y)
    have hMy := hM y (by simpa using hδ.le)
    have : ⟪(0 : EuclideanSpace ℝ (Fin d)), y⟫_ℝ - Λ 0 ≤ M := hy0.trans hMy
    simpa using this
  · set u : EuclideanSpace ℝ (Fin d) := (‖t‖)⁻¹ • t
    have htn : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
    have hu : ‖u‖ = 1 := by
      simp [u, norm_smul, abs_norm, inv_mul_cancel₀ htn]
    have hz : ‖(y + δ • u) - y‖ ≤ δ := by
      simp [u, norm_smul, Real.norm_eq_abs, abs_of_pos hδ, hu]
    have hbound := hM (y + δ • u) hz
    have hfy : ⟪t, y + δ • u⟫_ℝ - Λ t ≤ legendreTransform Λ (y + δ • u) :=
      le_legendreTransform Λ (y + δ • u) t (hbdd _)
    have hinner : ⟪t, δ • u⟫_ℝ = δ * ‖t‖ := by
      calc ⟪t, δ • u⟫_ℝ
          = δ * ⟪t, u⟫_ℝ := by simp [real_inner_smul_right]
        _ = δ * ⟪t, (‖t‖)⁻¹ • t⟫_ℝ := by rfl
        _ = δ * ((‖t‖)⁻¹ * ⟪t, t⟫_ℝ) := by simp [real_inner_smul_right]
        _ = δ * ((‖t‖)⁻¹ * ‖t‖ ^ 2) := by simp [real_inner_self_eq_norm_sq]
        _ = δ * ‖t‖ := by field_simp [htn]
    have hrew : ⟪t, y + δ • u⟫_ℝ - Λ t = (⟪t, y⟫_ℝ - Λ t) + δ * ‖t‖ := by
      rw [inner_add_right, hinner]; ring
    have : (⟪t, y⟫_ℝ - Λ t) + δ * ‖t‖ ≤ M := by
      calc (⟪t, y⟫_ℝ - Λ t) + δ * ‖t‖
          = ⟪t, y + δ • u⟫_ℝ - Λ t := hrew.symm
        _ ≤ legendreTransform Λ (y + δ • u) := hfy
        _ ≤ M := hbound
    linarith

/-- Global `hbdd` ⇒ FY is cocompact-coercive at every `y`. -/
theorem fy_tendsto_cocompact_atBot_of_forall_bddAbove {d : ℕ}
    (Λ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hbdd : ∀ x : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun l : EuclideanSpace ℝ (Fin d) => ⟪l, x⟫_ℝ - Λ l))
    (y : EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun t : EuclideanSpace ℝ (Fin d) => ⟪t, y⟫_ℝ - Λ t)
      (cocompact (EuclideanSpace ℝ (Fin d))) atBot := by
  let δ : ℝ := 1
  have hδ : (0 : ℝ) < δ := by norm_num
  obtain ⟨M, hM⟩ :=
    exists_ball_bound_legendreTransform_of_forall_bddAbove Λ hbdd y hδ
  refine tendsto_atBot.mpr fun N => ?_
  let R : ℝ := max 0 ((M - N) / δ + 1)
  refine mem_map.mpr <| mem_cocompact.mpr
    ⟨Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R, isCompact_closedBall _ _, ?_⟩
  intro t ht
  have htR : R < ‖t‖ := by
    have : ¬ ‖t‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using ht
    exact lt_of_not_ge this
  have hfy := fy_le_sub_mul_norm_of_ball_bound Λ y hδ hbdd hM t
  have hlarge : M - δ * ‖t‖ < N := by
    have hRbound : (M - N) / δ + 1 ≤ R := le_max_right _ _
    have hdiv : (M - N) / δ < R := lt_of_lt_of_le (lt_add_one _) hRbound
    have hMR : M - N < δ * R := by
      simpa [mul_comm] using (div_lt_iff₀ hδ).mp hdiv
    have hMt : M - N < δ * ‖t‖ := hMR.trans (mul_lt_mul_of_pos_left htR hδ)
    linarith
  have hle := hfy.trans hlarge.le
  simpa [Set.mem_preimage, Set.mem_setOf_eq] using hle

/-- Local coercivity from an explicit ball bound of Λ* at `y`.
Same recession as `fy_tendsto_cocompact_atBot_of_forall_bddAbove`, factored for reuse. -/
theorem fy_tendsto_cocompact_atBot_of_ball_bound {d : ℕ}
    (Λ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hbdd : ∀ x : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun l : EuclideanSpace ℝ (Fin d) => ⟪l, x⟫_ℝ - Λ l))
    (y : EuclideanSpace ℝ (Fin d)) {δ M : ℝ} (hδ : 0 < δ)
    (hM : ∀ z : EuclideanSpace ℝ (Fin d), ‖z - y‖ ≤ δ → legendreTransform Λ z ≤ M) :
    Tendsto (fun t : EuclideanSpace ℝ (Fin d) => ⟪t, y⟫_ℝ - Λ t)
      (cocompact (EuclideanSpace ℝ (Fin d))) atBot := by
  refine tendsto_atBot.mpr fun N => ?_
  let R : ℝ := max 0 ((M - N) / δ + 1)
  refine mem_map.mpr <| mem_cocompact.mpr
    ⟨Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R, isCompact_closedBall _ _, ?_⟩
  intro t ht
  have htR : R < ‖t‖ := by
    have : ¬ ‖t‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using ht
    exact lt_of_not_ge this
  have hfy := fy_le_sub_mul_norm_of_ball_bound Λ y hδ hbdd hM t
  have hlarge : M - δ * ‖t‖ < N := by
    have hRbound : (M - N) / δ + 1 ≤ R := le_max_right _ _
    have hdiv : (M - N) / δ < R := lt_of_lt_of_le (lt_add_one _) hRbound
    have hMR : M - N < δ * R := by
      simpa [mul_comm] using (div_lt_iff₀ hδ).mp hdiv
    have hMt : M - N < δ * ‖t‖ := hMR.trans (mul_lt_mul_of_pos_left htR hδ)
    linarith
  have hle := hfy.trans hlarge.le
  simpa [Set.mem_preimage, Set.mem_setOf_eq] using hle

/-- Under `HasFiniteMGF` + global `hbdd` (Λ* finite everywhere), FY is cocompact-coercive at every dual point.

**Scope (not HasFiniteMGF-only).** `HasFiniteMGF` (= ∀ t, ∫ exp⟨t,x⟩ < ∞) makes `Λ` finite and
continuous on all of `ℝᵈ`, but does **not** force `Λ*` finite everywhere: any non-degenerate
compactly supported law satisfies `HasFiniteMGF` while `Λ* = ∞` off `conv(supp)`. Degenerate /
lattice laws are similar on the affine hull. Cocompact FY coercivity at `y` needs
`y ∈ int(dom Λ*)` (local `hbdd` on a ball). Global `TiltCover` therefore takes `forall_bddAbove`
(= `Λ*` finite on all of `ℝᵈ`, e.g. Gaussian-type / full-dimensional unbounded support).
The public `(hMGF)(hbdd)` entry under that finite-Legendre hyp is the Lemma
`SatisfiesLDP_EmpiricalMeanLawPi.of.HasFiniteMGF.ForallBddAbove` (not bare `HasFiniteMGF`).
The ENNReal gate `CRF y < ∞` is vacuous (`ofReal` never `⊤`); the real finite-rate gate
remains `BddAbove` of FY. -/
theorem fy_tendsto_cocompact_atBot_of_HasFiniteMGF_of_forall_bddAbove {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t))
    (y : EuclideanSpace ℝ (Fin d)) :
    Tendsto
      (fun t : EuclideanSpace ℝ (Fin d) =>
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t)
      (cocompact (EuclideanSpace ℝ (Fin d))) atBot :=
  fy_tendsto_cocompact_atBot_of_forall_bddAbove
    (logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀) hbdd y

/-- `TiltCover` from `HasFiniteMGF` + finite Legendre everywhere (global `hbdd`).
Not HasFiniteMGF-only: see doc on `fy_tendsto_cocompact_atBot_of_HasFiniteMGF_of_forall_bddAbove`. -/
theorem TiltCover_of_HasFiniteMGF_of_forall_bddAbove {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t)) :
    TiltCover μ₀ hMGF :=
  TiltCover_of_fy_tendsto_cocompact_atBot μ₀ hMGF fun y _hy =>
    fy_tendsto_cocompact_atBot_of_HasFiniteMGF_of_forall_bddAbove μ₀ hMGF hbdd y

/-- Helper Cramér theorem with `hid` internalized under `HasFiniteMGF`.
Still needs Sanov-contraction `hLDP`. -/
theorem cramer_theorem_no_hid {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hcover : TiltCover μ₀ hMGF)
    (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t))
    (hLDP : SatisfiesLDP (fun n => empiricalMeanLawPi μ₀ n) (cramerRateFromSanov μ₀))
    (hRate : LowerSemicontinuous
      (cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀)) :
    SatisfiesLDP (fun n => empiricalMeanLawPi μ₀ n)
      (cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀) := by
  have heq := cramerRateFromSanov_eq_cramerRateFunction_of_tiltCover_no_hid
    μ₀ hMGF hcover hbdd
  exact hLDP.congr_rate heq hRate

/-- Residual wrapper that still takes an explicit Sanov-mean `hLDP`.
The public entry without `hLDP` is the Lemma
`SatisfiesLDP_EmpiricalMeanLawPi.of.HasFiniteMGF.ForallBddAbove` (signature `(hMGF)(hbdd)`). -/
theorem cramer_theorem_of_HasFiniteMGF_of_forall_bddAbove_of_meanSanovLDP {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t))
    (hLDP : SatisfiesLDP (fun n => empiricalMeanLawPi μ₀ n) (cramerRateFromSanov μ₀)) :
    SatisfiesLDP (fun n => empiricalMeanLawPi μ₀ n)
      (cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀) :=
  cramer_theorem_no_hid μ₀ hMGF
    (TiltCover_of_HasFiniteMGF_of_forall_bddAbove μ₀ hMGF hbdd) hbdd hLDP
    (lowerSemicontinuous_cramerRateFunction_of_HasFiniteMGF μ₀ hMGF hbdd)

/-! ### Compact finite sublevels of CRF (good-rate half) under HasFiniteMGF + forall_bddAbove -/

/-- Finite CRF-sublevels are bounded (linear coercivity from `Λ` continuous at `0`). -/
theorem isBounded_cramerRateFunction_le_ofReal_of_HasFiniteMGF_of_forall_bddAbove {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t))
    (a : ℝ) :
    Bornology.IsBounded
      {y : EuclideanSpace ℝ (Fin d) |
        cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y ≤ ENNReal.ofReal a} := by
  wlog ha : 0 ≤ a generalizing a
  · have h0a : (0 : ℝ≥0∞) ≤ ENNReal.ofReal a := bot_le
    have hmax : ENNReal.ofReal (max a 0) = ENNReal.ofReal a := by
      rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left h0a]
    simpa [hmax] using this (max a 0) (le_max_right _ _)
  let Λ := logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀
  have hΛ0 : Λ 0 = 0 := logMGFVec_zero (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀
  have hcont := continuous_logMGFVec_id_of_HasFiniteMGF μ₀ hMGF
  rcases (Metric.continuousAt_iff.mp hcont.continuousAt) (1 : ℝ) (by norm_num) with
    ⟨δ, hδpos, hδ⟩
  refine (Metric.isBounded_iff_subset_ball (0 : EuclideanSpace ℝ (Fin d))).mpr ?_
  refine ⟨(a + 1) / (δ / 2) + 1, ?_⟩
  intro y hy
  have hy' : legendreTransform Λ y ≤ a := by
    have : ENNReal.ofReal (legendreTransform Λ y) ≤ ENNReal.ofReal a := by
      simpa [cramerRateFunction] using hy
    exact (ENNReal.ofReal_le_ofReal_iff ha).mp this
  by_cases hy0 : y = 0
  · subst hy0
    exact Metric.mem_ball_self (by positivity)
  · have hx0 : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    let t : EuclideanSpace ℝ (Fin d) := ((δ / 2) / ‖y‖) • y
    have htnorm : ‖t‖ = δ / 2 := by
      change ‖((δ / 2) / ‖y‖) • y‖ = δ / 2
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (half_pos hδpos) hx0),
        div_mul_cancel₀ _ hx0.ne']
    have hΛt : Λ t < 1 := by
      have htδ : dist t (0 : EuclideanSpace ℝ (Fin d)) < δ := by
        rw [dist_eq_norm, sub_zero, htnorm]
        exact half_lt_self hδpos
      have hdist : dist (Λ t) (Λ 0) < 1 := hδ htδ
      have habs : |Λ t - Λ 0| < 1 := by simpa [Real.dist_eq] using hdist
      have : |Λ t| < 1 := by simpa [hΛ0, sub_zero] using habs
      exact (abs_lt.mp this).2
    have hcomp := le_legendreTransform Λ y t (hbdd y)
    have hinner : ⟪t, y⟫_ℝ = (δ / 2) * ‖y‖ := by
      change ⟪((δ / 2) / ‖y‖) • y, y⟫_ℝ = (δ / 2) * ‖y‖
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp [hx0.ne']
    have hlin : (δ / 2) * ‖y‖ - 1 ≤ legendreTransform Λ y := by
      have : ⟪t, y⟫_ℝ - Λ t ≤ legendreTransform Λ y := hcomp
      nlinarith [this, hinner, hΛt.le]
    have hlin' : (δ / 2) * ‖y‖ - 1 ≤ a := hlin.trans hy'
    have hδ2 : 0 < δ / 2 := half_pos hδpos
    have hdiv : ‖y‖ ≤ (a + 1) / (δ / 2) := (le_div_iff₀ hδ2).mpr (by linarith)
    refine Metric.mem_ball.mpr ?_
    rw [dist_eq_norm, sub_zero]
    exact lt_of_le_of_lt hdiv (lt_add_one _)

/-- Finite CRF-sublevels are compact. -/
theorem isCompact_cramerRateFunction_le_ofReal_of_HasFiniteMGF_of_forall_bddAbove {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t))
    (a : ℝ) :
    IsCompact
      {y : EuclideanSpace ℝ (Fin d) |
        cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y ≤ ENNReal.ofReal a} := by
  have hclosed : IsClosed
      {y | cramerRateFunction (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ y ≤ ENNReal.ofReal a} :=
    (lowerSemicontinuous_cramerRateFunction_of_HasFiniteMGF μ₀ hMGF hbdd).isClosed_preimage _
  have hbounded :=
    isBounded_cramerRateFunction_le_ofReal_of_HasFiniteMGF_of_forall_bddAbove μ₀ hMGF hbdd a
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbounded

/-- Finite Sanov-contracted sublevels are compact after rate ID. -/
theorem isCompact_cramerRateFromSanov_le_ofReal_of_HasFiniteMGF_of_forall_bddAbove {d : ℕ}
    (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ₀]
    (hMGF : HasFiniteMGF μ₀)
    (hbdd : ∀ y : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
        ⟪t, y⟫_ℝ - logMGFVec (fun x : EuclideanSpace ℝ (Fin d) => x) μ₀ t))
    (a : ℝ) :
    IsCompact
      {y : EuclideanSpace ℝ (Fin d) | cramerRateFromSanov μ₀ y ≤ ENNReal.ofReal a} := by
  have hcover := TiltCover_of_HasFiniteMGF_of_forall_bddAbove μ₀ hMGF hbdd
  have heq := funext
    (cramerRateFromSanov_eq_cramerRateFunction_of_tiltCover_no_hid μ₀ hMGF hcover hbdd)
  simpa [heq] using
    isCompact_cramerRateFunction_le_ofReal_of_HasFiniteMGF_of_forall_bddAbove μ₀ hMGF hbdd a
