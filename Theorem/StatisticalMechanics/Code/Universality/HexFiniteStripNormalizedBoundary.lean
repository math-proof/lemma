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


namespace StatMech.Universality

open Complex HexWalk


theorem hexLegalSAW_eq_nil_of_lastVertex_eq_first
    (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsaw : (ofTurns a h0 ts).IsLegalSAW)
    (hlast : hexInfra_midAccum a h0 ts
        + halfStep (hexInfra_headAccum h0 ts) = a + halfStep h0) :
    ts = [] := by
  cases ts with
  | nil => rfl
  | cons t ts =>
      exfalso
      have hnd : (verticesAux a h0 (t :: ts)).Nodup := hsaw.2
      rw [verticesAux_cons, List.nodup_cons] at hnd
      apply hnd.1
      have hmem := hexInfra_verticesAux_getLast_mem
        (a + halfStep h0 + halfStep (h0 + t)) (h0 + t) ts
      rw [← hexInfra_midAccum_cons, ← hexInfra_headAccum_cons, hlast] at hmem
      exact hmem

end StatMech.Universality
