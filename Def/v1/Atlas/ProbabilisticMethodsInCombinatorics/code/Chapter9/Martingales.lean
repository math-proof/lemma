/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/Martingales.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Moments.SubGaussian
public import Instance.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter9.Martingales

@[expose] public section

set_option maxHeartbeats 800000

open MeasureTheory Filter Set SimpleGraph


noncomputable section

namespace ShamirSpencer

/-- The Erdős–Rényi random graph measure $G(n, p)$ on simple graphs over $\{0, \dots, n-1\}$,
where each edge is included independently with probability $p \in [0, 1]$. -/
noncomputable def chromaticNumberNat (n : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  G.chromaticNumber.toNat

/-- **Definition 9.2.1** (Martingale). A sequence $(Z_n)_{n \ge 0}$ is a martingale with respect
to a filtration $(\mathcal F_n)$ and probability measure $\mu$ if each $Z_n$ is
$\mathcal F_n$-measurable, integrable, and $\mathbb{E}[Z_{n+1} \mid \mathcal F_n] = Z_n$.
This is a thin wrapper around Mathlib's `MeasureTheory.Martingale`. -/
def IsMartingale {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : MeasureTheory.Measure Ω) (ℱ : MeasureTheory.Filtration ℕ m0)
    (Z : ℕ → Ω → ℝ) : Prop :=
  MeasureTheory.Martingale Z ℱ μ

open Finset in

/-- The Hoeffding sub-Gaussian parameter $c^{2}/4$ for a centred random variable bounded in an
interval of length $c$, packaged as a non-negative real. -/
noncomputable def hoeffdingSubGParam (c : ℝ) (_ : 0 ≤ c) : NNReal :=
  ⟨c ^ 2 / 4, by positivity⟩

end ShamirSpencer
end
