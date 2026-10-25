/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Matchings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.Convex.Birkhoff
import Structure.v1.Atlas.AnAlgorithmistsToolkit.code.Matchings.Part4
open Finset


namespace Matchings

attribute [instance] BipartiteGraph.decAdj

namespace PartialMatching

variable {n : ℕ} {G : BipartiteGraph n} (M : PartialMatching G)

def chainIsAdj {n : ℕ} {G : BipartiteGraph n} (v w : ChainVertex G) : Prop :=
  v = w ∨
  (match v, w with
   | Sum.inl M, Sum.inr M' => M'.edges ⊆ M.edges
   | Sum.inr M', Sum.inl M => M'.edges ⊆ M.edges
   | Sum.inr M₁, Sum.inr M₂ =>
       (M₁.edges \ M₂.edges).card = 1 ∧ (M₂.edges \ M₁.edges).card = 1
   | Sum.inl _, Sum.inl _ => False
  )

def matchingSymDiff {n : ℕ} {G : BipartiteGraph n}
    (s t : PerfMatching G) : Finset (Fin n × Fin n) :=
  (s.edges \ t.edges) ∪ (t.edges \ s.edges)

def chainVertexEdges {n : ℕ} {G : BipartiteGraph n} : ChainVertex G → Finset (Fin n × Fin n)
  | Sum.inl m => m.edges
  | Sum.inr m => m.edges

end PartialMatching
end Matchings
