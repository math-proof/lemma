/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexVertexClassification.Part3


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators


structure HexFiniteRegion where
  
  verts : Finset ℂ
  
  mids : Finset ℂ
  
  start : ℂ
  
  start_mem : start ∈ mids
  

  vertexBound : ∀ w : HexWalk, (∀ m ∈ w.mids, m ∈ mids) →
    ∀ x ∈ w.vertices, x ∈ verts

end StatMech.Universality
