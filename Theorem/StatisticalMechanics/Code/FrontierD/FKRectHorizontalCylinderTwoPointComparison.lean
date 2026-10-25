/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTwoPointComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.BoxConnectionFullConnection
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4RadialDecay.Part4
import Abbrev.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTwoPointComparison
open MeasureTheory SimpleGraph
open scoped BigOperators


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section

theorem fkQgt4CriticalFree_infiniteTwoPointReal_eq_displacement
    {q : Real} (hq : 4 < q) (x y : Site 2) :
    FK.infiniteTwoPointReal
        (fkQgt4CriticalFreeMeasure hq :
          Measure (ConfigSpace (Sym2 (Site 2)))) x y =
      fkQgt4CriticalFreeTwoPoint hq (y - x) := by
  let hp := (BeffaraDC.selfDualPoint_mem_Ioo
    (by linarith : (0 : Real) < q)).1
  let hp1 := (BeffaraDC.selfDualPoint_mem_Ioo
    (by linarith : (0 : Real) < q)).2
  let hq0 : (0 : Real) < q := by linarith
  let hq1 : (1 : Real) <= q := by linarith
  let mu : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2 hp hp1 hq0
  have htrans : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site 2)) mu := by
    simpa [mu, hp, hp1, hq0] using
      (FK.fkgqt_freeIV_isTranslationInvariant
        (d := 2) hp hp1 hq1)
  have h := infiniteTwoPointReal_add_eq_of_translationInvariant
    mu htrans x (origin 2) (y - x)
  have hx0 : x + origin 2 = x := by
    funext i
    simp [origin]
  have hxy : x + (y - x) = y := by
    funext i
    simp
  rw [hx0, hxy] at h
  simpa [mu, hp, hp1, hq0, fkQgt4CriticalFreeMeasure,
    fkQgt4CriticalFreeTwoPoint] using h


theorem fkQgt4CriticalFree_boxConnEvent_le_displacement
    {q : Real} (hq : 4 < q) (radius : Nat)
    (x y : FK.boxVerts 2 radius) :
    ((fkQgt4CriticalFreeMeasure hq :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        (FK.boxConnEvent 2 radius x y) <=
      fkQgt4CriticalFreeTwoPoint hq (y.1 - x.1) := by
  calc
    _ <= FK.infiniteTwoPointReal
          (fkQgt4CriticalFreeMeasure hq :
            Measure (ConfigSpace (Sym2 (Site 2)))) x.1 y.1 :=
      FK.measureReal_boxConnEvent_le_infiniteTwoPointReal
        2 radius (fkQgt4CriticalFreeMeasure hq) x y
    _ = _ :=
      fkQgt4CriticalFree_infiniteTwoPointReal_eq_displacement hq x.1 y.1


end
end StatMech.FrontierD
