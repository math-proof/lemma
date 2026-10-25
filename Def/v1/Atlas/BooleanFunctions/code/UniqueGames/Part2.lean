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
import Instance.v1.Atlas.BooleanFunctions.code.UniqueGames


namespace UniqueGames

def numSatisfiedEdges {V : Type*} {W : Type*} {k : ℕ} [DecidableEq V] [DecidableEq W]
    (game : UniqueGame V W k) (labeling : Labeling V W k) : ℕ :=
  (game.edges.filter (fun p => edgeSatisfied game labeling p.1 p.2)).card

def numEdges {V : Type*} {W : Type*} [DecidableEq V] [DecidableEq W] {k : ℕ}
    (game : UniqueGame V W k) : ℕ :=
  game.edges.card

noncomputable def fractionSatisfied {V : Type*} {W : Type*} {k : ℕ}
    [DecidableEq V] [DecidableEq W]
    (game : UniqueGame V W k) (labeling : Labeling V W k) : ℝ :=
  (numSatisfiedEdges game labeling : ℝ) / (numEdges game : ℝ)

noncomputable def value {V : Type*} {W : Type*} {k : ℕ}
    [DecidableEq V] [DecidableEq W]
    (game : UniqueGame V W k) : ℝ :=
  iSup (fun labeling : Labeling V W k => fractionSatisfied game labeling)

opaque IsPolyTimeUniqueGameReduction {numV numW : ℕ → ℕ} {k : ℕ} :
  (∀ (m : ℕ), PCP.BinaryString m → UniqueGame (Fin (numV m)) (Fin (numW m)) k) → Prop

def IsNPHardGapUniqueGame (k : ℕ) (c s : ℝ) : Prop :=
  ∀ (L : PCP.Language), PCP.InNP L →
    ∃ (numV numW : ℕ → ℕ) (reduce : ∀ (m : ℕ), PCP.BinaryString m → UniqueGame (Fin (numV m)) (Fin (numW m)) k),
      IsPolyTimeUniqueGameReduction reduce ∧
      (∀ (m : ℕ) (x : PCP.BinaryString m), x ∈ L m → value (reduce m x) ≥ c) ∧
      (∀ (m : ℕ) (x : PCP.BinaryString m), x ∉ L m → value (reduce m x) ≤ s)

end UniqueGames
