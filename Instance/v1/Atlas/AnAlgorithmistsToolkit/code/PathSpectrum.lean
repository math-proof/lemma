/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/PathSpectrum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Def.v1.Atlas.AnAlgorithmistsToolkit.code.GraphMatrices
public import Theorem.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.GraphMatrices
public import Theorem.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.SpectraCommonGraphs
public import Instance.v1.Atlas.AnAlgorithmistsToolkit.code.SpectraCommonGraphs
@[expose] public section

open Real SimpleGraph Matrix Finset


namespace PathSpectrum

instance pathGraph_decRel (n : ℕ) : DecidableRel (pathGraph n).Adj := by
  intro u v
  rw [pathGraph_adj]
  exact instDecidableOr

end PathSpectrum
