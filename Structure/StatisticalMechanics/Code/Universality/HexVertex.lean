/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part4


namespace StatMech.Universality

open Complex


structure VertexWalkData where
  
  du : ℂ
  
  pairs : Finset ℕ
  
  pairWind : ℕ → ℤ
  
  pairLen : ℕ → ℕ
  
  triplets : Finset ℕ
  
  tripWind : ℕ → ℤ
  
  tripLen : ℕ → ℕ

end StatMech.Universality
