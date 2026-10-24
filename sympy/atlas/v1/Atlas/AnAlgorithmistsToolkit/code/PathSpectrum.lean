/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PathSpectrum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.atlas.v1.Atlas.AnAlgorithmistsToolkit.code.GraphMatrices
import Lemma.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.GraphMatrices
import Lemma.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.SpectraCommonGraphs
import sympy.atlas.v1.Atlas.AnAlgorithmistsToolkit.code.SpectraCommonGraphs

open Real SimpleGraph Matrix Finset

namespace PathSpectrum

instance pathGraph_decRel (n : ℕ) : DecidableRel (pathGraph n).Adj := by
  intro u v
  rw [pathGraph_adj]
  exact instDecidableOr

noncomputable section

def pathGraphEigenvalue (n : ℕ) (k : Fin n) : ℝ :=
  2 - 2 * cos (π * (k : ℝ) / (n : ℝ))

def pathGraphEigenvector (n : ℕ) (k : Fin n) (u : Fin n) : ℝ :=
  cos (π * (k : ℝ) * (2 * (u.val : ℝ) + 1) / (2 * (n : ℝ)))
