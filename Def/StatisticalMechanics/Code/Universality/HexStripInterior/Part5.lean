/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripInterior.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexW1ExitGeom.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexStripInterior.Part4


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


noncomputable def hexStrip_singleRight_straightSide (a : ℂ) (h0 : ℤ) (inReg : ℂ → Prop)
    (hclass : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inReg
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt
            (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) → ts = [(-1 : ℤ)]) :
    HexStraightSide inReg (hexStripInterior (hexStrip_singleRightDReg a h0)) a h0
      (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) :=
  hexStrip_straightSide (hexStrip_singleRightDReg a h0) inReg a h0
    (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) (h0 - 1)
    (hexStrip_singleRight_uniqueInterior a h0)
    (fun ts hadm => by
      have hts : ts = [(-1 : ℤ)] := hclass ts hadm
      subst hts; exact hexStrip_singleRight_staysInDir a h0)


end StatMech.Universality
