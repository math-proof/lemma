/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GroundUpWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.GroundUpWinding.Part3


namespace StatMech.Onsager.GroundUp

noncomputable def staircaseModel : RectPolygonData where
  Poly := ℕ
  size := fun k => k
  cc := fun k => (k : ℤ) + 4
  rc := fun k => (k : ℤ)
  simple := fun _ => True
  hcc := by intro k; positivity
  hrc := by intro k; positivity
  base := by intro k _ h; omega
  chord := by
    intro k _ hk
    
    refine ⟨k - 1, 0, trivial, trivial, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · push_cast [Nat.cast_sub (by omega : 1 ≤ k)]; ring
    · push_cast [Nat.cast_sub (by omega : 1 ≤ k)]; ring


end StatMech.Onsager.GroundUp
