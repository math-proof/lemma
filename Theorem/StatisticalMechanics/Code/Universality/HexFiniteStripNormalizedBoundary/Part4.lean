/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalization.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
import Theorem.StatisticalMechanics.Code.Universality.HexStripInterior.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Def.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part2


namespace StatMech.Universality

open Complex HexWalk


namespace HexFiniteRegion

theorem returningSAW_eq_nil_of_straightStart_reverse
    (R : HexFiniteRegion) (h0 : ℤ) (interior : ℂ → Prop)
    (S : HexStraightSide R.inRegion interior R.start h0 R.start)
    (hreverse : halfStep S.H = -halfStep h0) :
    ∀ ts : List ℤ,
      (ofTurns R.start h0 ts).IsLegalSAW
        ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion
        ∧ (ofTurns R.start h0 ts).EndsAt R.start → ts = [] := by
  intro ts hts
  cases ts with
  | nil => rfl
  | cons t ts =>
      have hdir := S.dir_eq t ts hts
      have hfinal : halfStep (hexInfra_headAccum h0 (t :: ts)) =
          -halfStep h0 := hdir.trans hreverse
      cases ts with
      | nil =>
          have ht : t = 1 ∨ t = -1 := hts.1.1 t (by simp)
          have hrev : halfStep (h0 + 3) = -halfStep h0 :=
            hexW1Exit_halfStep_add_three h0
          have heq : halfStep (h0 + t) = halfStep (h0 + 3) := by
            simpa only [hexInfra_headAccum_cons, hexInfra_headAccum_nil] using
              hfinal.trans hrev.symm
          have hdiv : (6 : ℤ) ∣ (h0 + t - (h0 + 3)) :=
            (hexUnit_eq_iff_mod _ _).mp (hexInfra_halfStep_inj heq)
          rcases ht with rfl | rfl <;> norm_num at hdiv
      | cons s ss =>
          have hend : hexInfra_midAccum R.start h0 (t :: s :: ss) =
              R.start := by
            rw [← hexInfra_endMid_eq_midAccum]
            exact hts.2.2
          have hpen := hexW1Exit_penult_mem
            (R.start + halfStep h0 + halfStep (h0 + t)) (h0 + t) s ss
          have hpen' :
              hexInfra_midAccum R.start h0 (t :: s :: ss)
                    - halfStep (hexInfra_headAccum h0 (t :: s :: ss)) ∈
                verticesAux
                  (R.start + halfStep h0 + halfStep (h0 + t))
                  (h0 + t) (s :: ss) := by
            simpa only [hexInfra_midAccum_cons, hexInfra_headAccum_cons] using hpen
          have hfirst : R.start + halfStep h0 ∈
              verticesAux
                (R.start + halfStep h0 + halfStep (h0 + t))
                (h0 + t) (s :: ss) := by
            rw [hend, hfinal] at hpen'
            convert hpen' using 1
            all_goals ring
          have hnd := hts.1.2
          change (verticesAux R.start h0 (t :: s :: ss)).Nodup at hnd
          rw [verticesAux_cons, List.nodup_cons] at hnd
          exact (hnd.1 hfirst).elim


end HexFiniteRegion
end StatMech.Universality
