/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/UniqueGames.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Def.v1.Atlas.BooleanFunctions.code.PCP.Part5
public import Theorem.v1.Atlas.BooleanFunctions.code.MISBound
public import Instance.v1.Atlas.BooleanFunctions.code.UniqueGames.Part3

@[expose] public section

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
