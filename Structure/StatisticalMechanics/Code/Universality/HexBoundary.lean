/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexBoundary


namespace StatMech.Universality

open Complex Filter Topology

open scoped Topology Real BigOperators


structure HexIncidence (V : Type*) where
  
  vtx : V
  
  edge : Fin 3
  deriving DecidableEq


structure HexDomain (V : Type*) where
  
  interiorVertices : Finset V
  
  pos : V → ℂ
  
  mid : V → Fin 3 → ℂ
  
  obs : ℂ → ℂ
  

  relation : ∀ v ∈ interiorVertices,
    ∑ j : Fin 3, (mid v j - pos v) * obs (mid v j) = 0

end StatMech.Universality
