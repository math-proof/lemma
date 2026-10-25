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
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.GraphMatrices
import Lemma.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.GraphMatrices
import Lemma.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.SpectraCommonGraphs
import Instance.v1.Atlas.AnAlgorithmistsToolkit.code.SpectraCommonGraphs
open Real SimpleGraph Matrix Finset


namespace PathSpectrum

instance pathGraph_decRel (n : ℕ) : DecidableRel (pathGraph n).Adj := by
  intro u v
  rw [pathGraph_adj]
  exact instDecidableOr

end PathSpectrum
