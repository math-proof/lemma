/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FiniteWitnessUnionBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
open Finset Set
open scoped BigOperators


namespace StatMech.Probability

noncomputable def finiteEventMass {Omega : Type*} [Fintype Omega]
    (mu : Omega -> Real) (A : Set Omega) : Real := by
  classical
  exact ∑ omega, if omega ∈ A then mu omega else 0


end StatMech.Probability
