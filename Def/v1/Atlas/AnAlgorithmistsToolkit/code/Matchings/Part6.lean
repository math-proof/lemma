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
import Inductive.v1.Atlas.AnAlgorithmistsToolkit.code.Matchings
open Finset


namespace Matchings

attribute [instance] BipartiteGraph.decAdj

namespace PartialMatching

variable {n : ℕ} {G : BipartiteGraph n} (M : PartialMatching G)

def partnerWitnessEquiv (n : ℕ) : PartnerWitness n ≃ (Unit ⊕ Fin n ⊕ (Fin n × Fin n)) where
  toFun := fun x => match x with
    | .self => Sum.inl ()
    | .reduced i => Sum.inr (Sum.inl i)
    | .reducedRotated i j => Sum.inr (Sum.inr (i, j))
  invFun := fun x => match x with
    | Sum.inl () => .self
    | Sum.inr (Sum.inl i) => .reduced i
    | Sum.inr (Sum.inr (i, j)) => .reducedRotated i j
  left_inv := fun x => by cases x <;> rfl
  right_inv := fun x => by
    rcases x with ⟨⟩ | (i | ⟨i, j⟩) <;> rfl

end PartialMatching
end Matchings
