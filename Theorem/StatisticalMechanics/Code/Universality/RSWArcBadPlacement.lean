/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcBadPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWArcJordanCyclic
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_contourArc_edges_cover
    {H : SimpleGraph (Site 2)} {u x y : Site 2}
    (c : H.Walk u u) (hx : x ∈ c.support) (hy : y ∈ c.support)
    {e : Sym2 (Site 2)} :
    e ∈ c.edges ↔
      e ∈ (rlc_orderedContourArc c hx hy).edges ∨
        e ∈ (rlc_complementaryContourArc c hx hy).edges := by
  let hy' : y ∈ (c.rotate x hx).support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c x hx).2 hy
  constructor
  · intro he
    have herot : e ∈ (c.rotate x hx).edges :=
      (SimpleGraph.Walk.rotate_edges c x hx).perm.mem_iff.mpr he
    rw [← SimpleGraph.Walk.take_spec (c.rotate x hx) hy',
      SimpleGraph.Walk.edges_append, List.mem_append] at herot
    rcases herot with heord | hecomp
    · exact Or.inl (by simpa [rlc_orderedContourArc] using heord)
    · exact Or.inr (by
        simpa [rlc_complementaryContourArc,
          SimpleGraph.Walk.edges_reverse] using hecomp)
  · rintro (heord | hecomp)
    · exact rlc_orderedContourArc_edges_subset c hx hy heord
    · exact rlc_complementaryContourArc_edges_subset c hx hy hecomp


end Universality
end StatMech
