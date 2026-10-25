/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexVertexClassification.Part3
import Def.StatisticalMechanics.Code.Universality.HexFiniteRegion


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators


namespace HexFiniteRegion

variable (R : HexFiniteRegion)


theorem vertices_mem (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hstay : (ofTurns a h0 ts).StaysIn R.inRegion) :
    ∀ x ∈ (ofTurns a h0 ts).vertices, x ∈ R.verts :=
  R.vertexBound (ofTurns a h0 ts) (fun m hm => hstay m hm)


theorem numVertices_le (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsaw : (ofTurns a h0 ts).IsSAW)
    (hstay : (ofTurns a h0 ts).StaysIn R.inRegion) :
    ts.length + 1 ≤ R.verts.card := by
  have hnd : (ofTurns a h0 ts).vertices.Nodup := hsaw
  have hlen : (ofTurns a h0 ts).vertices.length = ts.length + 1 := by
    rw [length_vertices]; simp
  have hmem : ∀ x ∈ (ofTurns a h0 ts).vertices, x ∈ R.verts :=
    R.vertices_mem a h0 ts hstay
  have hsub : (ofTurns a h0 ts).vertices.toFinset ⊆ R.verts := by
    intro x hx; exact hmem x (List.mem_toFinset.mp hx)
  calc ts.length + 1 = (ofTurns a h0 ts).vertices.length := hlen.symm
    _ = (ofTurns a h0 ts).vertices.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ R.verts.card := Finset.card_le_card hsub


theorem length_lt (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsaw : (ofTurns a h0 ts).IsSAW)
    (hstay : (ofTurns a h0 ts).StaysIn R.inRegion) :
    ts.length < R.verts.card := by
  have := R.numVertices_le a h0 ts hsaw hstay
  omega

end HexFiniteRegion
end StatMech.Universality
