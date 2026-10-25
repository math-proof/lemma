/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexVertexClassification.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part3


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators


noncomputable def hexFiniteRegion_single (a w : ℂ)
    (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) →
      ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ)) :
    HexFiniteRegion where
  verts := {w}
  mids := {a}
  start := a
  start_mem := Finset.mem_singleton_self a
  vertexBound := hclosure


end StatMech.Universality
