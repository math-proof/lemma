/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrip.lean -/

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
import Theorem.StatisticalMechanics.Code.RSW.Strip.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.RSWStrip
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip


def OverlapConnection (ω : ConfigSpace (Sym2 (Site 2))) (m m' c d : ℤ)
    (p q : Site 2) (hp : p ∈ rect m m' c d) (hq : q ∈ rect m m' c d) : Prop :=
  ConnectedWithin 2 ω (rect m m' c d) ⟨p, hp⟩ ⟨q, hq⟩


def overlapConnectionEvent (m m' c d : ℤ) (p q : Site 2)
    (hp : p ∈ rect m m' c d) (hq : q ∈ rect m m' c d) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | OverlapConnection ω m m' c d p q hp hq}


end Universality
end StatMech
