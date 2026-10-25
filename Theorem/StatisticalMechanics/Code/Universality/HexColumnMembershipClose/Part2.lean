/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexColumnMembershipClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexColumnMembershipClose


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


theorem hcm_verticesAux_translate (δ : ℂ) (m : ℂ) (h : ℤ) (ts : List ℤ) :
    verticesAux (m + δ) h ts = (verticesAux m h ts).map (· + δ) := by
  induction ts generalizing m h with
  | nil => simp [verticesAux_nil]; ring
  | cons t ts ih =>
    rw [verticesAux_cons, verticesAux_cons, List.map_cons, List.cons.injEq]
    refine ⟨by ring, ?_⟩
    rw [show m + δ + halfStep h + halfStep (h + t)
          = (m + halfStep h + halfStep (h + t)) + δ by ring]
    exact ih _ _


theorem hcm_spans_transl (m m' : ℂ) (h : ℤ) (T : ℕ) (ts : List ℤ) :
    hcm_SpansWidth m h T ts ↔ hcm_SpansWidth m' h T ts := by
  have hkey : m' = m + (m' - m) := by ring
  unfold hcm_SpansWidth HexWalk.ofTurns HexWalk.vertices
  simp only
  constructor
  · rintro ⟨u, hu, w, hw, hgap⟩
    rw [hkey, hcm_verticesAux_translate]
    refine ⟨u + (m' - m), List.mem_map_of_mem hu, w + (m' - m), List.mem_map_of_mem hw, ?_⟩
    simp only [Complex.add_re]; linarith
  · rintro ⟨u, hu, w, hw, hgap⟩
    rw [hkey, hcm_verticesAux_translate] at hu hw
    rw [List.mem_map] at hu hw
    obtain ⟨u0, hu0, hu0e⟩ := hu
    obtain ⟨w0, hw0, hw0e⟩ := hw
    refine ⟨u0, hu0, w0, hw0, ?_⟩
    rw [← hu0e, ← hw0e] at hgap
    simp only [Complex.add_re] at hgap; linarith


end StatMech.Universality
