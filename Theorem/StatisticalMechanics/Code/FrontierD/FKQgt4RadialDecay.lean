/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4RadialDecay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4DiagonalRate.Part3
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConnectionSymmetry
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4RadialDecay
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section

theorem fkQgt4CriticalFreeTwoPoint_pos
    {q : Real} (hq : 4 < q) (x : Site 2) :
    0 < fkQgt4CriticalFreeTwoPoint hq x := by
  unfold fkQgt4CriticalFreeTwoPoint FK.infiniteTwoPointReal
  exact FK.fkgq_freeInfiniteVolume_connection_pos
    (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
    (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
    (by linarith : (1 : Real) <= q) (origin 2) x


theorem fkQgt4CriticalFreeTwoPoint_add_supermultiplicative
    {q : Real} (hq : 4 < q) (x y : Site 2) :
    fkQgt4CriticalFreeTwoPoint hq x *
        fkQgt4CriticalFreeTwoPoint hq y <=
      fkQgt4CriticalFreeTwoPoint hq (x + y) := by
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
  have hshift : FK.infiniteTwoPointReal mu x (x + y) =
      fkQgt4CriticalFreeTwoPoint hq y := by
    have h := infiniteTwoPointReal_add_eq_of_translationInvariant
      mu htrans x (origin 2) y
    rw [show x + origin 2 = x by
          funext i
          simp [origin]] at h
    simpa [mu, hp, hp1, hq0,
      fkQgt4CriticalFreeTwoPoint] using h
  have hfkg := FK.fkgq_freeInfiniteVolume_connection_fkg
    hp hp1 hq1 (origin 2) x x (x + y)
  have hsubset :
      {omega | Connected 2 omega (origin 2) x} ∩
          {omega | Connected 2 omega x (x + y)} <=
        {omega | Connected 2 omega (origin 2) (x + y)} := by
    rintro omega ⟨hox, hxy⟩
    exact hox.trans hxy
  have hall := hfkg.trans (measureReal_mono (μ := mu) hsubset)
  change FK.infiniteTwoPointReal mu (origin 2) x *
      FK.infiniteTwoPointReal mu x (x + y) <=
        FK.infiniteTwoPointReal mu (origin 2) (x + y) at hall
  rw [hshift] at hall
  simpa [mu, hp, hp1, hq0, fkQgt4CriticalFreeTwoPoint,
    FK.infiniteTwoPointReal] using hall


theorem fkQgt4CriticalFreeTwoPoint_boxSym
    {q : Real} (hq : 4 < q) (S : FK.BoxSym 2) (x : Site 2) :
    fkQgt4CriticalFreeTwoPoint hq (S.τ x) =
      fkQgt4CriticalFreeTwoPoint hq x := by
  have h := FK.fkgq_freeInfiniteVolume_connection_boxSym
    (d := 2) (by norm_num) S
    (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
    (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
    (by linarith : (1 : Real) <= q) (origin 2) x
  have hzero : S.τ (origin 2) = origin 2 := by
    simpa [origin] using FK.rot_boxSym_fixes_zero S
  rw [hzero] at h
  simpa [fkQgt4CriticalFreeTwoPoint, FK.infiniteTwoPointReal] using h


end
end StatMech.FrontierD
