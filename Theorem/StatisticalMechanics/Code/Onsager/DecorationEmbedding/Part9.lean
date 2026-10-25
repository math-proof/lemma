/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Def.StatisticalMechanics.Code.Onsager.DecorationEmbedding.Part10


namespace StatMech.Onsager

@[simp] theorem ons_decMicroVertex_port
    (L : ℕ) (d : ons_Dart L) :
    ons_decMicroVertex L (ons_decPortMicroPoint L d) =
      ons_decEmbedVertex L d := by
  rcases d with ⟨p, mu⟩
  fin_cases mu <;>
    simp [ons_decPortMicroPoint, ons_decMicroVertex,
      ons_decEmbedVertex, ons_decEmbedOffset]

theorem ons_decPort_offset_not_mem
    (L : ℕ) (d : ons_Dart L) :
    ((ons_decPortMicroPoint L d).offsetX,
      (ons_decPortMicroPoint L d).offsetY) ∉ ons_decInteriorOffsets := by
  rcases d with ⟨p, mu⟩
  fin_cases mu <;>
    simp [ons_decPortMicroPoint, ons_decInteriorOffsets]


theorem ons_decEmbedVertex_not_mem_route_interior
    (L : ℕ) [Fact (2 < L)] (d f g : ons_Dart L)
    (hfg : (ons_decGraph L).Adj f g) :
    ons_decEmbedVertex L d ∉
      (ons_decEdgeRoute L f g hfg).support.tail.dropLast := by
  intro hd
  rw [ons_decEdgeRoute_interior_support] at hd
  rcases List.mem_map.mp hd with ⟨z, hz, hzeq⟩
  have hpz : ons_decPortMicroPoint L d = z :=
    ons_decMicroVertex_injective L
      ((ons_decMicroVertex_port L d).trans hzeq.symm)
  apply ons_decPort_offset_not_mem L d
  rw [hpz]
  exact ons_decEdgeInteriorData_offset_mem L f g hz

theorem ons_decEdgeRoute_tail_support
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e) :
    (ons_decEdgeRoute L d e hde).support.tail =
      (ons_decEdgeRoute L d e hde).support.tail.dropLast ++
        [ons_decEmbedVertex L e] := by
  rw [ons_decEdgeRoute_support]
  simp [ons_decEdgeRouteVertices]
  exact ons_decEdgeRoute_endpoint L d e hde

end StatMech.Onsager
