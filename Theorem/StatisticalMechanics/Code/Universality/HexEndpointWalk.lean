/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
import Def.StatisticalMechanics.Code.Universality.HexEndpointWalk


namespace StatMech.Universality

open HexWalk

namespace HexWalk

@[simp]
theorem endpointNumVertices_eq (w : HexWalk) :
    w.endpointNumVertices = w.turns.length := rfl

@[simp]
theorem length_endpointVertices (w : HexWalk) :
    w.endpointVertices.length = w.endpointNumVertices := by
  simp [endpointVertices, endpointNumVertices]


theorem endpointVerticesAux_append_one (m : ℂ) (h : ℤ) (ts : List ℤ) (t : ℤ) :
    (verticesAux m h (ts ++ [t])).dropLast = verticesAux m h ts := by
  induction ts generalizing m h with
  | nil => simp [verticesAux]
  | cons u us ih =>
      simp only [List.cons_append, verticesAux_cons]
      rw [List.dropLast_cons_of_ne_nil]
      · rw [ih]
      · have hlen := length_verticesAux
          (m + halfStep h + halfStep (h + u)) (h + u) (us ++ [t])
        intro hempty
        rw [hempty] at hlen
        simp at hlen

@[simp]
theorem endpointVertices_ofTurns_append_one (a : ℂ) (h0 : ℤ)
    (ts : List ℤ) (t : ℤ) :
    (ofTurns a h0 (ts ++ [t])).endpointVertices =
      (ofTurns a h0 ts).vertices := by
  exact endpointVerticesAux_append_one a h0 ts t


theorem endpointIsSAW_append_one_iff (a : ℂ) (h0 : ℤ)
    (ts : List ℤ) (t : ℤ) :
    (ofTurns a h0 (ts ++ [t])).EndpointIsSAW ↔
      (ofTurns a h0 ts).IsSAW := by
  simp [EndpointIsSAW, IsSAW]


theorem legalTurns_append_one_iff (a : ℂ) (h0 : ℤ)
    (ts : List ℤ) (t : ℤ) :
    (ofTurns a h0 (ts ++ [t])).LegalTurns ↔
      (ofTurns a h0 ts).LegalTurns ∧ (t = 1 ∨ t = -1) := by
  simp only [LegalTurns, ofTurns_turns, List.mem_append, List.mem_singleton]
  constructor
  · intro h
    exact ⟨fun u hu => h u (Or.inl hu), h t (Or.inr rfl)⟩
  · rintro ⟨h, ht⟩ u (hu | rfl)
    · exact h u hu
    · exact ht


theorem endpointIsLegalSAW_append_one_iff (a : ℂ) (h0 : ℤ)
    (ts : List ℤ) (t : ℤ) :
    (ofTurns a h0 (ts ++ [t])).EndpointIsLegalSAW ↔
      (ofTurns a h0 ts).IsLegalSAW ∧ (t = 1 ∨ t = -1) := by
  rw [EndpointIsLegalSAW, IsLegalSAW, legalTurns_append_one_iff,
    endpointIsSAW_append_one_iff]
  tauto


theorem endpoint_nil_isLegalSAW (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 []).EndpointIsLegalSAW := by
  constructor
  · intro t ht
    simp at ht
  · simp [EndpointIsSAW, endpointVertices, vertices, ofTurns]

end HexWalk
end StatMech.Universality
