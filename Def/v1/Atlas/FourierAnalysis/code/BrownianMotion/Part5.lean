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
import Structure.v1.Atlas.FourierAnalysis.code.BrownianMotion.Part3
open MeasureTheory ProbabilityTheory Complex Matrix
open scoped ENNReal NNReal


namespace GaussianLinearTransform

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

end GaussianLinearTransform
