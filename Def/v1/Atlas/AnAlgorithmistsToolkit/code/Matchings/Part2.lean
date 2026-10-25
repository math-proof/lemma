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
import Structure.v1.Atlas.AnAlgorithmistsToolkit.code.Matchings.Part2
open Finset


namespace Matchings

attribute [instance] BipartiteGraph.decAdj

namespace PartialMatching

variable {n : ℕ} {G : BipartiteGraph n} (M : PartialMatching G)

def matchedLeft : Finset (Fin n) := M.edges.image Prod.fst

def matchedRight : Finset (Fin n) := M.edges.image Prod.snd

def unmatchedLeft : Finset (Fin n) := Finset.univ \ M.matchedLeft

def unmatchedRight : Finset (Fin n) := Finset.univ \ M.matchedRight

def HasAugPath1 {n : ℕ} {G : BipartiteGraph n} (M : PartialMatching G) : Prop :=
  ∃ u v, u ∈ M.unmatchedLeft ∧ v ∈ M.unmatchedRight ∧ G.Adj u v

def HasAugPath3 {n : ℕ} {G : BipartiteGraph n} (M : PartialMatching G) : Prop :=
  ∃ u v u' v',
    u ∈ M.unmatchedLeft ∧ v ∈ M.unmatchedRight ∧
    (u', v') ∈ M.edges ∧ G.Adj u v' ∧ G.Adj u' v

def HasAugPathLE3 {n : ℕ} {G : BipartiteGraph n} (M : PartialMatching G) : Prop :=
  HasAugPath1 M ∨ HasAugPath3 M

end PartialMatching
end Matchings
