/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part11


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

@[simp] theorem hexCSBoundaryPair_piece
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (i : HexCSPairIndex T L) :
    (hexCSBoundaryPair T L hT hlocal hlaw i).piece = hexCSPairPiece i := by
  simp [hexCSBoundaryPair, HexMirrorBoundaryPair.piece, hexCSPairPiece,
    endpointMirrorBoundaryPair_of_reflection]

theorem hexCSBoundaryPair_mass_nonneg
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (i : HexCSPairIndex T L) :
    0 ≤ (hexCSBoundaryPair T L hT hlocal hlaw i).mass := by
  apply endpointMirrorBoundaryPair_mass_nonneg


theorem hexCSFixedIndex_heading_one {T L : ℕ} {hT : 0 < T}
    (k : HexCSFixedIndex T L hT) :
    hexCSCanonicalHeading k.1 = 1 := by
  have hedge : k.1.edge = 0 := by
    have he := congrArg (fun e : HexCSIncidence T L => e.edge) k.2.2.1
    change hexAWReflectEdge k.1.edge = k.1.edge at he
    exact (hexAWReflectEdge_fixed_iff k.1.edge).mp he
  have hcoord : hexAWReflectCoord k.1.vtx.1 = k.1.vtx.1 := by
    have hv := congrArg (fun e : HexCSIncidence T L => e.vtx.1) k.2.2.1
    simpa [hexCSReflectIncidence, hexCSReflectVertex] using hv
  have hij : k.1.vtx.1.i = k.1.vtx.1.j := by
    have hi := congrArg HexAWCoord.i hcoord
    symm
    simpa [hexAWReflectCoord] using hi
  obtain hleft | hright | hupp | hlow :=
    hexCS_boundary_classification k.1 k.2.1
  · exfalso
    apply k.2.2.2
    have hcoordOrigin : k.1.vtx.1 = hexAWOriginCoord := by
      have hzero : ∀ c : HexAWCoord,
          c.color = .black → c.i = c.j → hexAWDepth c = 0 →
            c = hexAWOriginCoord := by
        intro c hcolor hcij hdepth
        rcases c with ⟨i, j, color⟩
        simp only at hcolor hcij
        change -(i + j) = 0 at hdepth
        have hi : i = 0 := by omega
        have hj : j = 0 := by omega
        simp [hexAWOriginCoord, hi, hj, hcolor]
      exact hzero k.1.vtx.1 hleft.1 hij hleft.2.2
    rw [HexIncidence.mk.injEq]
    exact ⟨Subtype.ext hcoordOrigin, hedge⟩
  · rcases hright with ⟨hcolor, _, _⟩
    simp [hexCSCanonicalHeading, hcolor, hedge]
  · exact False.elim (by omega)
  · exact False.elim (by omega)

theorem hexCSFixedIndex_winding_zero {T L : ℕ} {hT : 0 < T}
    (k : HexCSFixedIndex T L hT) :
    hexCSCanonicalWinding k.1 = 0 := by
  rw [hexCSCanonicalWinding, hexCSFixedIndex_heading_one k]
  norm_num


end
end StatMech.Universality
