/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/BrownianMotion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ZetaValues
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.Liouville

import Mathlib.Analysis.Real.Pi.Bounds

open MeasureTheory ProbabilityTheory Complex Matrix
open scoped ENNReal NNReal

namespace GaussianLinearTransform

noncomputable def R_beta (β : ℝ) (m : ℕ) : ℝ :=
  ∫ r in (0:ℝ)..1, r ^ m * (1 - r) ^ β

structure HasIndependentGaussianIncrements
    {Ω : Type*} [MeasurableSpace Ω]
    (B : NNReal → Ω → ℝ) (P : Measure Ω) : Prop where
  zero_at_origin : ∀ ω, B 0 ω = 0
  indep_increments : ∀ (n : ℕ) (t : Fin (n + 1) → NNReal),
    StrictMono t → t 0 = 0 →
    iIndepFun (m := fun (_ : Fin n) => inferInstance)
      (fun (j : Fin n) (ω : Ω) => B (t j.succ) ω - B (t j.castSucc) ω) P
  gaussian_increments : ∀ (n : ℕ) (t : Fin (n + 1) → NNReal),
    StrictMono t → t 0 = 0 →
    ∀ (j : Fin n), HasLaw
      (fun ω => B (t j.succ) ω - B (t j.castSucc) ω)
      (gaussianReal 0 (t j.succ - t j.castSucc)) P

structure HasBrownianCharacterization
    {Ω : Type*} [MeasurableSpace Ω]
    (B : NNReal → Ω → ℝ) (P : Measure Ω) : Prop where
  zero_at_origin : ∀ ω, B 0 ω = 0
  gaussian_process : IsGaussianProcess B P
  mean_zero : ∀ (t : NNReal), ∫ ω, B t ω ∂P = 0
  covariance : ∀ (s t : NNReal), ∫ ω, B s ω * B t ω ∂P = min (s : ℝ) (t : ℝ)

noncomputable def partialSumCLM {α : Type*} [Fintype α] (n : ℕ) (pos : α → Fin (n + 1)) :
    (Fin n → ℝ) →L[ℝ] (α → ℝ) where
  toFun v a := ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < (pos a).val), v k
  map_add' x y := by ext a; simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c x := by
    ext a; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; rw [Finset.mul_sum]
  cont := by
    apply continuous_pi; intro a; apply continuous_finset_sum; intro k _
    exact (ContinuousLinearMap.proj (R := ℝ) k).continuous

structure IsIIDStdGaussian {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (P : Measure Ω) : Prop where
  indep : iIndepFun (m := fun _ => inferInstance) a P
  std_gaussian : ∀ k, HasLaw (a k) (gaussianReal 0 1) P

noncomputable def randomPowerSeries {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (z : ℂ) (ω : Ω) : ℂ :=
  ∑' k : ℕ, (a (k + 1) ω : ℂ) * z ^ (k + 1) / (↑(k + 1 : ℕ) : ℂ)

noncomputable def powerSeriesDeriv {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (z : ℂ) (ω : Ω) : ℂ :=
  ∑' j : ℕ, (a (j + 1) ω : ℂ) * z ^ j

noncomputable def weightedGradientIntegral {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (β : ℝ) (ω : Ω) : ℝ :=
  ∫ t in (0 : ℝ)..(2 * Real.pi),
    ∫ r in (0 : ℝ)..1,
      (4 * ‖powerSeriesDeriv a (↑r * Complex.exp (↑t * Complex.I)) ω‖ ^ 4) *
      (1 - r) ^ β * r

noncomputable def weightedGradientIntegralENNReal {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (β : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ t : ℝ in Set.Icc 0 (2 * Real.pi),
    ∫⁻ r : ℝ in Set.Icc 0 1,
      ENNReal.ofReal
        ((4 * ‖powerSeriesDeriv a (↑r * Complex.exp (↑t * Complex.I)) ω‖ ^ 4) *
         (1 - r) ^ β * r)

/-- A real-valued Gaussian random variable with law $\mathcal{N}(0, v)$ lies in $L^2(P)$. -/
lemma memLp_two_of_hasLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {v : ℝ≥0} (hlaw : HasLaw X (gaussianReal 0 v) P) :
    MemLp X 2 P :=
  hlaw.hasGaussianLaw.memLp_two

/-- The partial sum $S_n = \sum_{k < n} X_k$ of Gaussian random variables lies in $L^2(P)$. -/
lemma memLp_partialSum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0}
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P) (n : ℕ) :
    MemLp (fun ω => ∑ k ∈ range n, X k ω) 2 P :=
  memLp_finset_sum _ (fun k _ => memLp_two_of_hasLaw (hgauss k))


/-- The partial sum $S_n = \sum_{k < n} X_k$ viewed as an element of $L^2(P)$. -/
noncomputable def partialSumLp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0}
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P) (n : ℕ) :
    Lp ℝ 2 P :=
  (memLp_partialSum hgauss n).toLp _


set_option maxHeartbeats 800000 in

/-- Predicate characterizing a Rademacher-type random variable $R : Ω → ℝ$ on
$(Ω, P)$: $R$ is measurable, has mean zero $\mathbb{E}[R] = \int R\,\mathrm{d}P = 0$,
and unit variance $\mathbb{E}[R^2] = \int R^2\,\mathrm{d}P = 1$. The canonical
example is the symmetric $\pm 1$ Bernoulli (Rademacher) variable. -/
structure IsRademacher {Ω : Type*} [MeasurableSpace Ω] (R : Ω → ℝ) (P : Measure Ω) : Prop where
  measurable : Measurable R
  mean_zero : ∫ ω, R ω ∂P = 0
  variance_one : ∫ ω, (R ω) ^ 2 ∂P = 1

/-- The $k$-th partial sum (random walk) of a sequence $(R_i)_{i \in ℕ}$ of random
variables: $S_k(ω) = \sum_{i < k} R_i(ω)$. -/
noncomputable def randomWalk {Ω : Type*} (R : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ range k, R i ω

/-- The Donsker-scaled increment of the random walk between indices $k_{\text{prev}}$
and $k_{\text{next}}$:
$$\frac{S_{k_{\text{next}}}(ω) - S_{k_{\text{prev}}}(ω)}{\sqrt{n}}.$$
This is the basic building block whose distribution converges to a Gaussian as
$n \to \infty$. -/
noncomputable def scaledIncrement {Ω : Type*} (R : ℕ → Ω → ℝ) (n : ℕ)
    (k_prev k_next : ℕ) (ω : Ω) : ℝ :=
  (randomWalk R k_next ω - randomWalk R k_prev ω) / Real.sqrt n

/-- The discrete grid index associated with a continuous time $t_j$ at scale $n$:
$\lfloor n \cdot t_j \rfloor$. Converts a continuous time partition into the nearest
discrete step on the random walk. -/
noncomputable def gridIndex (n : ℕ) (t : Fin (m + 1) → ℝ) (j : Fin (m + 1)) : ℕ :=
  ⌊(n : ℝ) * t j⌋₊

/-- The vector of variances $\sigma_j^2 = t_{j+1} - t_j$ for $j = 0, \dots, m-1$
associated with a strictly increasing time partition $t : \mathrm{Fin}(m+1) \to ℝ$.
These are the variances of the limiting independent Gaussian increments in Brownian
finite-dimensional distribution convergence. -/
noncomputable def varianceVector {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : StrictMono t) :
    Fin m → NNReal :=
  fun j => ⟨t j.succ - t j.castSucc,
    le_of_lt (sub_pos.mpr (ht Fin.castSucc_lt_succ))⟩

/-- **Brownian FDD convergence (discrete version).** For iid Rademacher random
variables $(R_i)$, the vector of scaled increments on a partition
$0 \le t_0 < t_1 < \cdots < t_m$ converges jointly in distribution to a vector of
independent Gaussians with variances $\sigma_j^2 = t_{j+1} - t_j$. This combines
the one-dimensional CLT on each block (`increment_tendstoInDistribution_gaussianReal`)
with the joint-from-marginal-with-independence principle
(`indep_marginal_tendstoInDistribution_product`). -/
noncomputable def piecewiseLinearInterp {Ω : Type*} (R : ℕ → Ω → ℝ) (n : ℕ)
    (t : ℝ) (ω : Ω) : ℝ :=
  let k := ⌊(n : ℝ) * t⌋₊
  let frac := (n : ℝ) * t - ↑k
  randomWalk R k ω / Real.sqrt n + frac * R k ω / Real.sqrt n

/-- The continuous-time increment of the piecewise linear interpolation between
times $t_{\text{prev}}$ and $t_{\text{next}}$: $f_n(t_{\text{next}}) - f_n(t_{\text{prev}})$. -/
noncomputable def fnIncrement {Ω : Type*} (R : ℕ → Ω → ℝ) (n : ℕ)
    (t_prev t_next : ℝ) (ω : Ω) : ℝ :=
  piecewiseLinearInterp R n t_next ω - piecewiseLinearInterp R n t_prev ω

def SatisfiesGradientBound (F : ℂ → ℂ) (C : ℝ) (α : ℝ) : Prop :=
  ∀ z : ℂ, ‖z‖ < 1 → ‖fderiv ℝ F z‖ ≤ C * (1 - ‖z‖) ^ (-1 + α)

noncomputable def wienerC0 : ℝ := Real.sqrt (1 / Real.pi)

noncomputable def wienerC1 : ℝ := Real.sqrt (2 / Real.pi)

noncomputable def wienerProcess {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  wienerC0 * a 0 ω * t +
    wienerC1 * ∑' k : ℕ, a (k + 1) ω * Real.sin ((↑(k + 1)) * t) / (↑(k + 1))

structure IsWienerBrownianMotion {Ω : Type*} [MeasurableSpace Ω]
    (W : ℝ → Ω → ℝ) (P : Measure Ω) : Prop where
  zero_at_origin : ∀ ω, W 0 ω = 0
  mean_zero : ∀ t, 0 ≤ t → t ≤ Real.pi → ∫ ω, W t ω ∂P = 0
  gaussian_linear_comb : ∀ (n : ℕ) (t : Fin n → ℝ),
    (∀ j, 0 ≤ t j ∧ t j ≤ Real.pi) → ∀ (c : Fin n → ℝ),
    HasGaussianLaw (fun ω => ∑ j, c j * W (t j) ω) P
  covariance_eq_min : ∀ s t, 0 ≤ s → s ≤ Real.pi → 0 ≤ t → t ≤ Real.pi →
    ∫ ω, W s ω * W t ω ∂P = min s t
  ae_continuousOn : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) (Icc 0 Real.pi)

noncomputable def wienerCoeff (n : ℕ) (t : Fin n → ℝ) (c : Fin n → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then wienerC0 * ∑ j : Fin n, c j * t j
  else wienerC1 * ∑ j : Fin n, c j * Real.sin (↑k * t j) / ↑k

noncomputable def wienerCoeffVar (n : ℕ) (t : Fin n → ℝ) (c : Fin n → ℝ) : ℕ → ℝ≥0 :=
  fun k => ⟨(wienerCoeff n t c k) ^ 2, sq_nonneg _⟩

noncomputable def wienerBasisCoeff (s : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then wienerC0 * s
  else wienerC1 * Real.sin (↑k * s) / ↑k
