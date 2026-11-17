/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Matchings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fin.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Analysis.Convex.Birkhoff
public import Def.v1.Atlas.AnAlgorithmistsToolkit.code.Matchings

@[expose] public section

open Finset


namespace Matchings

attribute [instance] BipartiteGraph.decAdj

structure PartialMatching {n : ℕ} (G : BipartiteGraph n) where
  edges : Finset (Fin n × Fin n)
  edge_adj : ∀ p ∈ edges, G.Adj p.1 p.2
  left_inj : ∀ ⦃p q⦄, p ∈ edges → q ∈ edges → p.1 = q.1 → p = q
  right_inj : ∀ ⦃p q⦄, p ∈ edges → q ∈ edges → p.2 = q.2 → p = q

end Matchings
