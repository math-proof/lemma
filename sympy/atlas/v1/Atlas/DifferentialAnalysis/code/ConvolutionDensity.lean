/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionDensity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.ConvolutionDensityFix
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.ConvolutionDensityFix
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.TestFunctions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzCutoffConvergence
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.TestFunctions
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.SchwartzCutoffConvergence
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

open scoped ZeroAtInfty Convolution
open MeasureTheory Filter Topology Function Set TestFunctions

noncomputable section

namespace ConvolutionDensity

/-- The cocompact filter on Euclidean space is countably generated: it has a
countable basis given by complements of closed balls of integer radius. -/
instance cocompact_eucl_countablyGenerated {n : ℕ} :
    (Filter.cocompact (EuclideanSpace ℝ (Fin n))).IsCountablyGenerated := by
  apply Filter.HasCountableBasis.isCountablyGenerated (ι := ℕ)
    (p := fun _ => True)
    (s := fun m => (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) m)ᶜ)
  exact {
    countable := Set.countable_univ.mono (fun _ _ => trivial)
    toHasBasis := {
      mem_iff' := by
        intro S; simp only [true_and]
        constructor
        · intro hS
          rw [Filter.mem_cocompact] at hS
          obtain ⟨K, hK, hKS⟩ := hS
          obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
          obtain ⟨m, hm⟩ := exists_nat_ge r
          exact ⟨m, fun x hx => hKS fun hxK => by
            simp only [Set.mem_compl_iff, Metric.mem_closedBall, not_le] at hx
            exact absurd (le_trans (hr hxK) hm) (not_le.mpr hx)⟩
        · rintro ⟨m, hm⟩
          exact Filter.mem_cocompact.mpr
            ⟨Metric.closedBall 0 m, isCompact_closedBall 0 m, hm⟩
    }
  }

/-- `CkNormBdd n k f` is the recursive predicate stating that all derivatives
of `f : EuclideanSpace ℝ (Fin n) → ℂ` up to order `k` are bounded; that is,
`f` is `k` times differentiable and `f` together with all its partial
derivatives up to order `k` have bounded norm ranges. -/
def CkNormBdd (n : ℕ) : ℕ → (EuclideanSpace ℝ (Fin n) → ℂ) → Prop
  | 0, f => BddAbove (Set.range fun x => ‖f x‖)
  | k + 1, f =>
    CkNormBdd n k f ∧
      Differentiable ℝ f ∧
      ∀ j : Fin n, CkNormBdd n k fun x => fderiv ℝ f x (EuclideanSpace.single j 1)

/-- Multiplication of a Schwartz function `f` by a compactly-supported smooth
real-valued function `φ`. The result is again Schwartz with compact support
contained in the support of `φ`. -/
noncomputable def SchwartzMap.cutoffMul (φ : E → ℝ) (hφcs : HasCompactSupport φ)
    (hφcd : ContDiff ℝ ⊤ φ) (f : SchwartzMap E F) : SchwartzMap E F :=
  (hφcs.smul_right (f' := ⇑f)).toSchwartzMap
    ((hφcd.of_le le_top).smul f.smooth')

/-- The Plancherel isometry: the `L²` Fourier transform on a real
finite-dimensional inner product space `V` is a `ℂ`-linear isometric
equivalence of `L²(V; ℂ)` with itself. This is the operator-theoretic
incarnation of the Plancherel theorem. -/
def fourierL2Equiv : (Lp (α := V) ℂ 2) ≃ₗᵢ[ℂ] (Lp (α := V) ℂ 2) :=
  MeasureTheory.Lp.fourierTransformₗᵢ V ℂ

end ConvolutionDensity
