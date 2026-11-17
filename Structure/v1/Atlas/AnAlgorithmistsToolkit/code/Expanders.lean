/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Expanders.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Fintype.Prod
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Def.v1.Atlas.AnAlgorithmistsToolkit.code.Expanders


public section

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
