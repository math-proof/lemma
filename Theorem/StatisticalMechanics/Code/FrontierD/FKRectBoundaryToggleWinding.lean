/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryToggleWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.PermSameCycleWeightSplit
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryCycleWeight.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialToggle.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialClosedCycles.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleExact
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedOpenBoundaryDependence
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingInsertion.Part2
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem not_windingIndependent_of_pos_nsmul_left
    (n : Nat) (hn : 0 < n) (u v : Int × Int)
    (h : ¬ FKRectWindingIndependent (n • u) v) :
    ¬ FKRectWindingIndependent u v := by
  unfold FKRectWindingIndependent at h ⊢
  push_neg at h ⊢
  rw [Prod.smul_fst, Prod.smul_snd] at h
  simp only [nsmul_eq_mul] at h
  have hnint : (0 : Int) < n := by exact_mod_cast hn
  nlinarith

theorem not_windingIndependent_nsmul_left
    (n : Nat) (u v : Int × Int)
    (h : ¬ FKRectWindingIndependent u v) :
    ¬ FKRectWindingIndependent (n • u) v := by
  unfold FKRectWindingIndependent at h ⊢
  push_neg at h ⊢
  rw [Prod.smul_fst, Prod.smul_snd]
  simp only [nsmul_eq_mul]
  calc
    (n : Int) * u.1 * v.2 - (n : Int) * u.2 * v.1 =
        (n : Int) * (u.1 * v.2 - u.2 * v.1) := by ring
    _ = 0 := by rw [h]; ring

theorem not_windingIndependent_add_left
    (u w v : Int × Int)
    (hu : ¬ FKRectWindingIndependent u v)
    (hw : ¬ FKRectWindingIndependent w v) :
    ¬ FKRectWindingIndependent (u + w) v := by
  unfold FKRectWindingIndependent at hu hw ⊢
  push_neg at hu hw ⊢
  simp only [Prod.fst_add, Prod.snd_add]
  linear_combination hu + hw

end
end StatMech.FrontierD
