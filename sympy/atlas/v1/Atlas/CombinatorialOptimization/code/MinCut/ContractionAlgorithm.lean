/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/MinCut/ContractionAlgorithm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open Finset

namespace MinCut

structure Multigraph (V : Type*) [Fintype V] [DecidableEq V] where
  edgeMult : V → V → ℕ
  symm : ∀ u v, edgeMult u v = edgeMult v u
  no_loops : ∀ v, edgeMult v v = 0

variable {V : Type*} [Fintype V] [DecidableEq V]

def Multigraph.degree (G : Multigraph V) (v : V) : ℕ :=
  ∑ u : V, G.edgeMult v u

def Multigraph.cutValue (G : Multigraph V) (S : Finset V) : ℕ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, G.edgeMult u v

def Multigraph.IsMinCut (G : Multigraph V) (S : Finset V) : Prop :=
  S.Nonempty ∧ S ≠ Finset.univ ∧
  ∀ T : Finset V, T.Nonempty → T ≠ Finset.univ → G.cutValue S ≤ G.cutValue T

noncomputable def Multigraph.contractionSurvivalProb (G : Multigraph V) (S : Finset V) : ℝ :=
  (1 - (G.cutValue S : ℝ) / ((∑ v : V, G.degree v : ℝ) / 2)) ^ (Fintype.card V - 2)
