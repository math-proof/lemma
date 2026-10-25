/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanConvexBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PathVisitsRow.Part2
import Theorem.StatisticalMechanics.Code.Universality.HVIntersection.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanStripInduction.Part9
import Theorem.StatisticalMechanics.Code.Lattice.ArcMonotonise
import Def.StatisticalMechanics.Code.Lattice.JordanConvexBox.Part2
open Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


theorem jcb_vsFix_arc_sides_of_vCrossing (ω : ConfigSpace (Sym2 (Site 2))) {α β m m' c d : ℤ}
    (hαm : α ≤ m) (hm'β : m' < β)
    (hres : ∀ (xB : Site 2) (hxB : xB ∈ rect m m' c d),
      JcbColShift ω m m' c d xB hxB) :
    StatMech.Universality.vsFix_arc_sides ω α β m m' c d := by
  intro _hαm' _hmm' _hm'β' xB hxB hxBbot yT hyT hcV
  have hcd : c ≤ d := by have := mem_rect.mp hxB; omega
  obtain ⟨col, hlo, hhi, hon, hcorner, hc1, hshift⟩ := hres xB hxB
  have hsep : ArcSeparatingSet (overlapComp ω m m' c d xB hxB) α β c d :=
    jcb_separatingSide_of_vCrossing hαm hm'β hcd col hlo hhi hon hcorner hc1 hshift
  obtain ⟨S, hSleft, hSright, hSedge⟩ := hsep
  exact ⟨S, hSleft, hSright, hSedge⟩


theorem jcb_colShift_of_shift (ω : ConfigSpace (Sym2 (Site 2))) {m m' c d : ℤ}
    {xB yT : Site 2} (hxB : xB ∈ rect m m' c d) (hyT : yT ∈ rect m m' c d)
    (hxBc : xB 1 = c) (hyTd : yT 1 = d)
    (hcV : ConnectedWithin 2 ω (rect m m' c d) ⟨xB, hxB⟩ ⟨yT, hyT⟩)
    (col : ℤ → ℤ)
    (hcol : col = (jcb_rowData_of_vCrossing ω hxB hyT hxBc hyTd hcV).choose)
    (hshift : ∀ r : ℤ,
      col (r + 1) - col r = 1 ∨ col (r + 1) - col r = 0 ∨ col (r + 1) - col r = -1) :
    JcbColShift ω m m' c d xB hxB := by
  obtain ⟨hlo, hhi, hon, hcorner, hc1⟩ :=
    (jcb_rowData_of_vCrossing ω hxB hyT hxBc hyTd hcV).choose_spec
  subst hcol
  exact ⟨_, hlo, hhi, hon, hcorner, hc1, hshift⟩

end Lattice
end StatMech
