/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.HVIntersection.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ArcSides.Part3
import Theorem.StatisticalMechanics.Code.Lattice.TwoPathsCrossWinding.Part2
import Def.StatisticalMechanics.Code.Lattice.JordanStripInduction.Part6
open Set SimpleGraph MeasureTheory


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


theorem jsi_arc_sides_of_hasMonotone (ω : ConfigSpace (Sym2 (Site 2))) {α β m m' c d : ℤ}
    (hαm : α ≤ m) (hm'β : m' < β) (h : JsiHasMonotoneArc ω m m' c d) :
    StatMech.Universality.vsFix_arc_sides ω α β m m' c d :=
  tpc_arc_sides_of_sep ω
    (fun xB hxB => jsi_separatingSide hαm hm'β (h xB hxB).some.toJsiRowArc)


theorem jsi_arc_sides_of_rowArc (ω : ConfigSpace (Sym2 (Site 2))) {α β m m' c d : ℤ}
    (hαm : α ≤ m) (hm'β : m' < β)
    (A : ∀ (xB : Site 2) (hxB : xB ∈ rect m m' c d),
      JsiRowArc (overlapComp ω m m' c d xB hxB) m m' c d) :
    StatMech.Universality.vsFix_arc_sides ω α β m m' c d :=
  tpc_arc_sides_of_sep ω (fun xB hxB => jsi_separatingSide hαm hm'β (A xB hxB))


theorem jsi_rsw_strip_glue_of_rowArc
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) {a m m' b c d : ℤ}
    (ham : a < m) (hmm' : m ≤ m') (hm'b : m' < b)
    (AL : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (xB : Site 2) (hxB : xB ∈ rect m m' c d),
      JsiRowArc (overlapComp ω m m' c d xB hxB) m m' c d)
    (AR : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (xB : Site 2) (hxB : xB ∈ rect m m' c d),
      JsiRowArc (overlapComp ω m m' c d xB hxB) m m' c d) :
    μ.real (horizontalCrossingEvent a m' c d)
        * μ.real (verticalCrossingEvent m m' c d)
        * μ.real (horizontalCrossingEvent m b c d)
      ≤ μ.real (horizontalCrossingEvent a b c d) :=
  tpc_rsw_strip_glue_of_sep μ hpa (le_of_lt ham) hmm' (le_of_lt hm'b)
    (fun ω xB hxB => jsi_separatingSideLt ham (le_refl m') (AL ω xB hxB))
    (fun ω xB hxB => jsi_separatingSide (le_refl m) hm'b (AR ω xB hxB))

end Lattice
end StatMech
