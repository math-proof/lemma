/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.Strip
open Set MeasureTheory SimpleGraph


namespace StatMech

namespace RSW

namespace Strip

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.Universality


def LeftHalfCrossing (ω : ConfigSpace (Sym2 (Site 2))) (a m c d : ℤ) (z : Site 2)
    (hz : z ∈ rect a m c d) : Prop :=
  ∃ xL : leftSide a m c d,
    ConnectedWithin 2 ω (rect a m c d) ⟨xL, leftSide_subset xL.2⟩ ⟨z, hz⟩


def RightHalfCrossing (ω : ConfigSpace (Sym2 (Site 2))) (m b c d : ℤ) (z : Site 2)
    (hz : z ∈ rect m b c d) : Prop :=
  ∃ yR : rightSide m b c d,
    ConnectedWithin 2 ω (rect m b c d) ⟨z, hz⟩ ⟨yR, rightSide_subset yR.2⟩


def leftHalfCrossingEvent (a m c d : ℤ) (z : Site 2) (hz : z ∈ rect a m c d) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | LeftHalfCrossing ω a m c d z hz}


def rightHalfCrossingEvent (m b c d : ℤ) (z : Site 2) (hz : z ∈ rect m b c d) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | RightHalfCrossing ω m b c d z hz}


end Strip
end RSW
end StatMech
