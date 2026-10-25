/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TwoPathsCrossWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.HVIntersection.Part2
import Theorem.StatisticalMechanics.Code.Universality.VSeparatesFixed.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ArcSides.Part3
import Def.StatisticalMechanics.Code.Lattice.TwoPathsCrossWinding
open Set SimpleGraph MeasureTheory


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


theorem tpc_two_paths_cross_of_sep {P : Set (Site 2)} {α β c d : ℤ}
    (hsep : ArcSeparatingSet P α β c d)
    {x y : Site 2} (hx : x ∈ rect α β c d) (hy : y ∈ rect α β c d)
    (hx0 : x 0 = α) (hy0 : y 0 = β)
    (γ : (hypercubicLattice 2).Walk x y)
    (hsupp : ∀ z ∈ γ.support, z ∈ rect α β c d) :
    ∃ z ∈ γ.support, z ∈ P := by
  obtain ⟨S, hSleft, hSright, hSedge⟩ := hsep
  refine tpc_meets_of_separating_set γ (hSleft x hx hx0) (hSright y hy hy0) ?_
  intro u v hadj hemem hbd
  have hu : u ∈ rect α β c d := hsupp u (γ.fst_mem_support_of_mem_edges hemem)
  have hv : v ∈ rect α β c d := hsupp v (γ.snd_mem_support_of_mem_edges hemem)
  exact hSedge u v hu hv hadj hbd


theorem tpc_arc_sides_of_sep (ω : ConfigSpace (Sym2 (Site 2))) {α β m m' c d : ℤ}
    (hsep : ∀ (xB : Site 2) (hxB : xB ∈ rect m m' c d),
      ArcSeparatingSet (overlapComp ω m m' c d xB hxB) α β c d) :
    StatMech.Universality.vsFix_arc_sides ω α β m m' c d := by
  intro _hαm _hmm' _hm'β xB hxB _hxBbot _yT _hyT _hcV
  obtain ⟨S, hSleft, hSright, hSedge⟩ := hsep xB hxB
  exact ⟨S, hSleft, hSright, hSedge⟩


theorem tpc_rsw_strip_glue_of_sep
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) {a m m' b c d : ℤ}
    (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hsepL : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (xB : Site 2) (hxB : xB ∈ rect m m' c d),
      ArcSeparatingSet (overlapComp ω m m' c d xB hxB) a m' c d)
    (hsepR : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (xB : Site 2) (hxB : xB ∈ rect m m' c d),
      ArcSeparatingSet (overlapComp ω m m' c d xB hxB) m b c d) :
    μ.real (horizontalCrossingEvent a m' c d)
        * μ.real (verticalCrossingEvent m m' c d)
        * μ.real (horizontalCrossingEvent m b c d)
      ≤ μ.real (horizontalCrossingEvent a b c d) :=
  vsFix_rsw_strip_glue_of_arc_sides μ hpa ham hmm' hm'b
    (fun ω => tpc_arc_sides_of_sep ω (hsepL ω))
    (fun ω => tpc_arc_sides_of_sep ω (hsepR ω))

end Lattice
end StatMech
