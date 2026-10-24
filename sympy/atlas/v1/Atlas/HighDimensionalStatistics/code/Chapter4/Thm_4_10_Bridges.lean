/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_10_Bridges.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Thm_4_6
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter4.Thm_4_6
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory ProbabilityTheory Matrix Real Finset BigOperators

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Rigollet.Chapter4.Thm_4_10_Bridges

variable {d : ℕ}

/-- Operator (spectral) norm of a real square matrix, defined as the supremum of
$\|Av\|$ over unit vectors $v \in \mathbb{R}^d$. -/
def matOpNorm (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ⨆ (v : EuclideanSpace ℝ (Fin d)) (_ : ‖v‖ = 1),
    ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v)‖

/-- Canonical equivalence between `Fin S.card` and the subset `S ⊆ Fin d`,
obtained from the order isomorphism that enumerates `S` in increasing order. -/
def finsetEquivFin (S : Finset (Fin d)) : Fin S.card ≃ S :=
  (Finset.orderIsoOfFin S rfl).toEquiv

/-- Restrict a random vector $X : \Omega \to \mathbb{R}^d$ to the coordinates
indexed by `S ⊆ Fin d`, viewed as a vector in $\mathbb{R}^m$ where $m = |S|$. -/
def restrictVec {Ω : Type*} (S : Finset (Fin d)) (hcard : S.card = m)
    (X : Ω → Fin d → ℝ) : Ω → Fin m → ℝ :=
  fun ω j => X ω ((finsetEquivFin S) (j.cast hcard.symm))

/-- Restrict a sample $X_1, \ldots, X_n$ of random vectors in $\mathbb{R}^d$ to the
coordinates indexed by `S ⊆ Fin d`, yielding a sample in $\mathbb{R}^m$. -/
def restrictSamples {Ω : Type*} {n : ℕ} (S : Finset (Fin d)) (hcard : S.card = m)
    (X : Fin n → Ω → Fin d → ℝ) : Fin n → Ω → Fin m → ℝ :=
  fun i => restrictVec S hcard (X i)
