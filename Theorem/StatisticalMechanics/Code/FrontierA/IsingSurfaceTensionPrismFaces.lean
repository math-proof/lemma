/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismGeometry.Part3
import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part7
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismFaces


namespace StatMech.FrontierA

open scoped BigOperators

open StatMech StatMech.Ising

noncomputable section

theorem sum_boundaryDegree_mul_eq_oddRectangularPrismFaceSum
    (n : Nat)
    (f : RectangularPrismSite (2 * n + 1) (2 * n + 1) n -> Real) :
    (∑ v, (rectangularPrismBoundaryDegree v : Real) * f v) =
      oddRectangularPrismFaceSum n f := by
  rw [sum_rectangularPrismSite_eq]
  simp only [rectangularPrismBoundaryDegree, Nat.cast_add, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, add_mul,
    Finset.sum_add_distrib]
  have hlastSucc (x : Fin (2 * n + 1)) :
      x.val + 1 = 2 * n + 1 ↔ x = Fin.last (2 * n) := by
    constructor
    · intro hx
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    · intro hx
      simp [hx]
  have hlastSuccEq (x : Fin (2 * n + 1)) :
      (x.val + 1 = 2 * n + 1) = (x = Fin.last (2 * n)) :=
    propext (hlastSucc x)
  simp_rw [hlastSuccEq]
  simp [oddRectangularPrismFaceSum, Fin.last]


theorem rectangularPrismPlusBoundaryInteraction_eq_faces
    (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    rectangularPrismPlusBoundaryInteraction sigma =
      oddRectangularPrismFaceInteraction n sigma := by
  simpa [rectangularPrismPlusBoundaryInteraction,
    oddRectangularPrismFaceInteraction] using
    sum_boundaryDegree_mul_eq_oddRectangularPrismFaceSum n (spin sigma)


end
end StatMech.FrontierA
