/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/UniqueGames.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Archimedean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.BigOperators.Field
import Def.v1.Atlas.BooleanFunctions.code.PCP.Part5
import Theorem.v1.Atlas.BooleanFunctions.code.MISBound
import Instance.v1.Atlas.BooleanFunctions.code.UniqueGames.Part3


namespace UniqueGames

variable {X : Type*} [DecidableEq X] [Fintype X] {k : ℕ}

def IsTAssignment (A : X → Finset (Fin k)) (X' : Finset X) (t : ℕ) : Prop :=
  ∀ x ∈ X', (A x).card = t

noncomputable def NonBipartiteUniqueGame.fractionTSatisfiedWithin
    (game : NonBipartiteUniqueGame X k) (X' : Finset X)
    (A : X → Finset (Fin k)) : ℝ :=
  ((game.edgesWithin X').filter (fun e => game.edgeTSatisfiedBy A e)).card /
    (game.edgesWithin X').card

def StrongUGC_YES (game : NonBipartiteUniqueGame X k) (ε : ℝ) : Prop :=
  ∃ X' : Finset X,
    (X'.card : ℝ) ≥ (1 - ε) * ((Finset.univ : Finset X).card : ℝ) ∧
    ∃ A : X → Fin k, ∀ e ∈ game.edgesWithin X', game.edgeSatisfiedBy A e

def StrongUGC_NO (game : NonBipartiteUniqueGame X k) (ε : ℝ) (t : ℕ) : Prop :=
  ∀ X' : Finset X,
    (X'.card : ℝ) ≥ ε * ((Finset.univ : Finset X).card : ℝ) →
    ∀ A : X → Finset (Fin k), IsTAssignment A X' t →
      ∃ e ∈ game.edgesWithin X', ¬ game.edgeTSatisfiedBy A e

opaque IsPolyTimeNonBipartiteUGReduction {numX : ℕ → ℕ} {k : ℕ} :
  (∀ (m : ℕ), PCP.BinaryString m → NonBipartiteUniqueGame (Fin (numX m)) k) → Prop

def StrongUGC : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ k t : ℕ, ∀ (L : PCP.Language), PCP.InNP L →
      ∃ (numX : ℕ → ℕ) (reduce : ∀ (m : ℕ), PCP.BinaryString m → NonBipartiteUniqueGame (Fin (numX m)) k),
        IsPolyTimeNonBipartiteUGReduction reduce ∧
        (∀ (m : ℕ) (x : PCP.BinaryString m), x ∈ L m →
          StrongUGC_YES (reduce m x) ε) ∧
        (∀ (m : ℕ) (x : PCP.BinaryString m), x ∉ L m →
          StrongUGC_NO (reduce m x) ε t)

end UniqueGames
