/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Def.StatisticalMechanics.Code.RSW.Defs.Part4
open Set


namespace StatMech

namespace RSW

namespace Box

open StatMech.Lattice

open StatMech.TwoDim


@[simp] theorem mem_dualHorizontalCrossingEvent {a b c d : ℤ}
    {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ dualHorizontalCrossingEvent a b c d ↔ DualHorizontalCrossing ω a b c d := Iff.rfl

@[simp] theorem mem_dualVerticalCrossingEvent {a b c d : ℤ}
    {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ dualVerticalCrossingEvent a b c d ↔ DualVerticalCrossing ω a b c d := Iff.rfl


theorem dualHorizontalCrossing_iff (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ) :
    DualHorizontalCrossing ω a b c d ↔ HorizontalCrossing (dualConfig ω) a b c d := Iff.rfl


theorem dualVerticalCrossing_iff (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ) :
    DualVerticalCrossing ω a b c d ↔ VerticalCrossing (dualConfig ω) a b c d := Iff.rfl


theorem dualHorizontalCrossingEvent_increasing {a b c d : ℤ}
    {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : dualConfig ω ≤ dualConfig ω')
    (hω : ω ∈ dualHorizontalCrossingEvent a b c d) :
    ω' ∈ dualHorizontalCrossingEvent a b c d :=
  horizontalCrossingEvent_increasing h hω


theorem dualVerticalCrossingEvent_increasing {a b c d : ℤ}
    {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : dualConfig ω ≤ dualConfig ω')
    (hω : ω ∈ dualVerticalCrossingEvent a b c d) :
    ω' ∈ dualVerticalCrossingEvent a b c d :=
  verticalCrossingEvent_increasing h hω


end Box
end RSW
end StatMech
