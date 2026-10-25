/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWeightedDirichletComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison.Part5
open Finset SimpleGraph


namespace StatMech.Universality

noncomputable section

noncomputable def isingFiniteWeightedLaplacian
    {V : Type*} [Fintype V]
    (conductance : V → V → Real) (f : V → Real) (x : V) : Real := by
  classical
  exact ∑ y, conductance x y * (f y - f x)

def IsingFiniteWeightedSubharmonicOn
    {V : Type*} [Fintype V]
    (conductance : V → V → Real) (boundary : V → Prop)
    (f : V → Real) : Prop :=
  ∀ x, ¬ boundary x → 0 ≤ isingFiniteWeightedLaplacian conductance f x

def IsingFiniteWeightedSuperharmonicOn
    {V : Type*} [Fintype V]
    (conductance : V → V → Real) (boundary : V → Prop)
    (f : V → Real) : Prop :=
  ∀ x, ¬ boundary x → isingFiniteWeightedLaplacian conductance f x ≤ 0

def IsingFiniteWeightedHarmonicOn
    {V : Type*} [Fintype V]
    (conductance : V → V → Real) (boundary : V → Prop)
    (f : V → Real) : Prop :=
  ∀ x, ¬ boundary x → isingFiniteWeightedLaplacian conductance f x = 0

end
end StatMech.Universality
