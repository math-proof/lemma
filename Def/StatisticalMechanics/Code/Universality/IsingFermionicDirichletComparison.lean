/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDirichletComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveIntegration
open Finset SimpleGraph


namespace StatMech.Universality

noncomputable section

noncomputable def isingFiniteGraphLaplacian
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (f : V → ℝ) (x : V) : ℝ := by
  classical
  exact ∑ y ∈ G.neighborFinset x, (f y - f x)

def IsingFiniteGraphSubharmonicOn
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (boundary : V → Prop) (f : V → ℝ) : Prop :=
  ∀ x, ¬ boundary x → 0 ≤ isingFiniteGraphLaplacian G f x

def IsingFiniteGraphSuperharmonicOn
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (boundary : V → Prop) (f : V → ℝ) : Prop :=
  ∀ x, ¬ boundary x → isingFiniteGraphLaplacian G f x ≤ 0

def IsingFiniteGraphHarmonicOn
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (boundary : V → Prop) (f : V → ℝ) : Prop :=
  ∀ x, ¬ boundary x → isingFiniteGraphLaplacian G f x = 0


end
end StatMech.Universality
