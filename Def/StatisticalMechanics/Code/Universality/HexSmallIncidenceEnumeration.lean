/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexStartPhaseRepair.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryUncond.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexSmallIncidenceEnumeration


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators


def hexFiniteStripCoreContourPart
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing}
    (C : HexFiniteStripBoundaryCore R h0 D P) (k : Fin 5) (z : ℂ) : Prop :=
  (k = 0 ∧ z = R.start)
    ∨ (k = 1 ∧ z ∈ C.sides.bottom)
    ∨ (k = 2 ∧ z ∈ C.sides.slantPlus)
    ∨ (k = 3 ∧ z ∈ C.sides.slantMinus)
    ∨ (k = 4 ∧ z ∈ C.sides.top)


end StatMech.Universality
