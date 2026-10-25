/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Expanders.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.Expanders


namespace SpectralExpanders

structure GraphFamily where
  V : ℕ → Type*
  instFintype : ∀ n, Fintype (V n)
  instDecidableEq : ∀ n, DecidableEq (V n)
  G : ∀ n, SimpleGraph (V n)
  instDecidableAdj : ∀ n, DecidableRel (G n).Adj
  d : ℕ
  isRegular : ∀ n, (G n).IsRegularOfDegree d
  card_ge_two : ∀ n, @Fintype.card (V n) (instFintype n) ≥ 2

end SpectralExpanders
