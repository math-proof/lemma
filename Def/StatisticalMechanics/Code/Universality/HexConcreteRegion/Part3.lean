/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexPairingMaps.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part3


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators


noncomputable def hexConcrete_region (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
    HexFiniteRegion where
  verts := {hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0}
  mids := {a, hexConcreteQ a h0, hexConcreteR a h0}
  start := a
  start_mem := by simp
  vertexBound := hclosure


end StatMech.Universality
