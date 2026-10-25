/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GroundUpWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.GroundUpWinding.Part2


namespace StatMech.Onsager.GroundUp

structure RectPolygonData where
  
  Poly : Type
  
  size : Poly → ℕ
  
  cc : Poly → ℤ
  
  rc : Poly → ℤ
  
  simple : Poly → Prop
  
  hcc : ∀ P, 0 ≤ cc P
  
  hrc : ∀ P, 0 ≤ rc P
  

  base : ∀ P, simple P → rc P = 0 → cc P = 4
  


  chord : ∀ P, simple P → 0 < rc P →
    ∃ P₁ P₂, simple P₁ ∧ simple P₂ ∧
      size P₁ < size P ∧ size P₂ < size P ∧
      cc P₁ + cc P₂ = cc P + 3 ∧ rc P₁ + rc P₂ = rc P - 1


end StatMech.Onsager.GroundUp
