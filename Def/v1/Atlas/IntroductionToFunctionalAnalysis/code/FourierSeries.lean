/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/FourierSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Measure.Haar.Unique
variable {T : ℝ} [hT : Fact (0 < T)]

open MeasureTheory AddCircle Finset Filter Complex


namespace FourierSeries

/-- The `N`-th partial Fourier sum of a function `f : AddCircle T → ℂ`, defined as
`S_N f(x) = ∑_{n = -N}^{N} ĉ_n(f) · e^{2πi n x / T}`, where `ĉ_n(f) = fourierCoeff f n`. -/
noncomputable def partialFourierSum (f : AddCircle T → ℂ) (N : ℕ) :
    AddCircle T → ℂ :=
  fun x => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff f n • fourier n x

/-- The `N`-th Cesàro–Fourier mean of `f`, given by
`σ_N f(x) = (N+1)⁻¹ · ∑_{k=0}^{N} S_k f(x)`,
where `S_k f` is the `k`-th partial Fourier sum. -/
noncomputable def cesaroFourierMean (f : AddCircle T → ℂ) (N : ℕ) :
    AddCircle T → ℂ :=
  fun x => ((N : ℂ) + 1)⁻¹ • ∑ k ∈ range (N + 1), partialFourierSum f k x

/-- The Fejér kernel `K_N`, defined here as the Cesàro mean of the Dirichlet kernels:
`K_N(x) = (N+1)⁻¹ · ∑_{k=0}^{N} ∑_{n=-k}^{k} e^{2πi n x / T}`. Equivalently (after
algebra), `K_N(x) = (N+1)⁻¹ · (sin((N+1)x/2) / sin(x/2))²` away from the origin. -/
noncomputable def fejerKernel (N : ℕ) : AddCircle T → ℂ :=
  fun x => ((N : ℂ) + 1)⁻¹ • ∑ k ∈ range (N + 1),
    ∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), fourier n x

end FourierSeries
