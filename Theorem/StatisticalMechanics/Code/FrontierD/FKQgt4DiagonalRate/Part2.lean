/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiagonalRate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4DiscontinuityAssembly.Part3
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConnectionFKG
import Mathlib.Analysis.Subadditive
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4DiagonalRate.Part2
open MeasureTheory Filter Topology


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section

theorem fkQgt4CriticalFreeExactDiagonalTwoPoint_pos
    {q : Real} (hq : 4 < q) (n : Nat) :
    0 < fkQgt4CriticalFreeExactDiagonalTwoPoint hq n := by
  unfold fkQgt4CriticalFreeExactDiagonalTwoPoint FK.infiniteTwoPointReal
  exact FK.fkgq_freeInfiniteVolume_connection_pos
    (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
    (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
    (by linarith : (1 : Real) <= q) (origin 2)
    (fkQgt4ExactDiagonalSite n)

theorem fkQgt4CriticalFreeExactDiagonalTwoPoint_le_one
    {q : Real} (hq : 4 < q) (n : Nat) :
    fkQgt4CriticalFreeExactDiagonalTwoPoint hq n <= 1 :=
  measureReal_le_one


theorem infiniteTwoPointReal_add_eq_of_translationInvariant
    {d : Nat} (mu : Measure (ConfigSpace (Sym2 (Site d))))
    (htrans : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site d)) mu)
    (a x y : Site d) :
    FK.infiniteTwoPointReal mu (a + x) (a + y) =
      FK.infiniteTwoPointReal mu x y := by
  let g : Multiplicative (Site d) := Multiplicative.ofAdd a
  have hx : g • x = a + x := rfl
  have hy : g • y = a + y := rfl
  have hpre :
      (ConfigSpace.shift g : ConfigSpace (Sym2 (Site d)) ->
        ConfigSpace (Sym2 (Site d))) ⁻¹'
          {omega | Connected d omega (a + x) (a + y)} =
        {omega | Connected d omega x y} := by
    ext omega
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [← hx, ← hy]
    exact connected_shift g omega x y
  have hinv := htrans.measure_preimage g
    (measurableSet_connected (a + x) (a + y))
  unfold FK.infiniteTwoPointReal Measure.real
  rw [hpre] at hinv
  exact congrArg ENNReal.toReal hinv.symm


theorem fkQgt4CriticalFreeExactDiagonalTwoPoint_supermultiplicative
    {q : Real} (hq : 4 < q) (m n : Nat) :
    fkQgt4CriticalFreeExactDiagonalTwoPoint hq m *
        fkQgt4CriticalFreeExactDiagonalTwoPoint hq n <=
      fkQgt4CriticalFreeExactDiagonalTwoPoint hq (m + n) := by
  let hp := (BeffaraDC.selfDualPoint_mem_Ioo
    (by linarith : (0 : Real) < q)).1
  let hp1 := (BeffaraDC.selfDualPoint_mem_Ioo
    (by linarith : (0 : Real) < q)).2
  let hq0 : (0 : Real) < q := by linarith
  let hq1 : (1 : Real) <= q := by linarith
  let mu : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2 hp hp1 hq0
  let x := fkQgt4ExactDiagonalSite m
  let y := fkQgt4ExactDiagonalSite (m + n)
  have htrans : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site 2)) mu := by
    simpa [mu, hp, hp1, hq0] using
      (FK.fkgqt_freeIV_isTranslationInvariant
        (d := 2) hp hp1 hq1)
  have hshift : FK.infiniteTwoPointReal mu x y =
      fkQgt4CriticalFreeExactDiagonalTwoPoint hq n := by
    have h := infiniteTwoPointReal_add_eq_of_translationInvariant
      mu htrans x (origin 2) (fkQgt4ExactDiagonalSite n)
    rw [show x + origin 2 = x by
          funext i
          simp [origin],
      show x + fkQgt4ExactDiagonalSite n = y by
        dsimp [x, y]
        rw [← fkQgt4ExactDiagonalSite_add]] at h
    simpa [mu, hp, hp1, hq0, x, y,
      fkQgt4CriticalFreeExactDiagonalTwoPoint] using h
  have hfkg := FK.fkgq_freeInfiniteVolume_connection_fkg
    hp hp1 hq1 (origin 2) x x y
  have hsubset :
      {omega | Connected 2 omega (origin 2) x} ∩
          {omega | Connected 2 omega x y} <=
        {omega | Connected 2 omega (origin 2) y} := by
    rintro omega ⟨hox, hxy⟩
    exact hox.trans hxy
  have hmeasure := measureReal_mono (μ := mu) hsubset
  have hall := hfkg.trans hmeasure
  change FK.infiniteTwoPointReal mu (origin 2) x *
      FK.infiniteTwoPointReal mu x y <=
        FK.infiniteTwoPointReal mu (origin 2) y at hall
  rw [hshift] at hall
  simpa [mu, hp, hp1, hq0, x, y,
    fkQgt4CriticalFreeExactDiagonalTwoPoint,
    FK.infiniteTwoPointReal] using hall


theorem fkQgt4CriticalFreeExactDiagonalNegLog_subadditive
    {q : Real} (hq : 4 < q) :
    Subadditive (fun n =>
      -Real.log (fkQgt4CriticalFreeExactDiagonalTwoPoint hq n)) := by
  intro m n
  have hm := fkQgt4CriticalFreeExactDiagonalTwoPoint_pos hq m
  have hn := fkQgt4CriticalFreeExactDiagonalTwoPoint_pos hq n
  have hmn := fkQgt4CriticalFreeExactDiagonalTwoPoint_pos hq (m + n)
  have hsuper :=
    fkQgt4CriticalFreeExactDiagonalTwoPoint_supermultiplicative hq m n
  have hlog := Real.strictMonoOn_log.monotoneOn
    (mul_pos hm hn) hmn hsuper
  rw [Real.log_mul hm.ne' hn.ne'] at hlog
  linarith

theorem fkQgt4CriticalFreeExactDiagonalNegLog_bddBelow
    {q : Real} (hq : 4 < q) :
    BddBelow (Set.range (fun n =>
      -Real.log (fkQgt4CriticalFreeExactDiagonalTwoPoint hq n) /
        (n : Real))) := by
  refine ⟨0, ?_⟩
  rintro z ⟨n, rfl⟩
  have hpos := fkQgt4CriticalFreeExactDiagonalTwoPoint_pos hq n
  have hone := fkQgt4CriticalFreeExactDiagonalTwoPoint_le_one hq n
  have hneg : 0 <= -Real.log
      (fkQgt4CriticalFreeExactDiagonalTwoPoint hq n) := by
    linarith [Real.log_nonpos hpos.le hone]
  exact div_nonneg hneg (Nat.cast_nonneg n)


end
end StatMech.FrontierD
