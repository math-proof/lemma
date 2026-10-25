/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripIncidenceObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryPhases.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripIncidenceObstruction.Part3


namespace StatMech.Universality

open Complex HexWalk Set


def hexFiniteStripContourPart
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing}
    (B : HexFiniteStripBoundaryData R h0 D P) (k : Fin 5) (z : ℂ) : Prop :=
  (k = 0 ∧ z = R.start)
    ∨ (k = 1 ∧ z ∈ B.sides.bottom)
    ∨ (k = 2 ∧ z ∈ B.sides.slantPlus)
    ∨ (k = 3 ∧ z ∈ B.sides.slantMinus)
    ∨ (k = 4 ∧ z ∈ B.sides.top)


end StatMech.Universality
