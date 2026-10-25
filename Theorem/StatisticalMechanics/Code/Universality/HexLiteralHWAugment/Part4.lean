/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part4


namespace StatMech.Universality

open HexWalk


theorem hlha_verticesAux_coord (p d : HexReturnCoord) (m s : ℂ)
    (h : ℤ) (ts : List ℤ)
    (hdir : halfStep h = d.value * s)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    verticesAux m h ts =
      (hlha_coordVertices p d ts).map (hlha_realizeCoord m s h p) := by
  induction ts generalizing p d m h with
  | nil =>
      simp [verticesAux, hlha_coordVertices, hlha_realizeCoord]
  | cons t ts ih =>
      have ht := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      let e := d.turn t
      have he : halfStep (h + t) = e.value * s :=
        hexReturn_halfStep_turn s h d t hdir ht
      rw [verticesAux_cons, hlha_coordVertices, List.map_cons]
      congr 1
      · simp [hlha_realizeCoord]
      · rw [ih (p.add e) e
          (m + halfStep h + halfStep (h + t)) (h + t) he htail]
        apply List.map_congr_left
        intro r _
        unfold hlha_realizeCoord
        rw [he, HexReturnCoord.value_add]
        ring

end StatMech.Universality
