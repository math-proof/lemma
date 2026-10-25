/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickInnerFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickFaces.Part3
import Def.StatisticalMechanics.Code.FK.TriHexBrickInnerFaces.Part2
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls

noncomputable section

theorem triHexBrickInnerFaceMap_injective
    {N m : Nat} (hNm : N < m) :
    Function.Injective (triHexBrickInnerFaceMap N m) := by
  intro t u htu
  have hrep : BeffaraDC.pfdFace (triHexPlanarFiniteStarPlanar m)
      (hexagonalBrickFaceLeft t.1) =
      triHexPlanarFiniteStarFace m u.1 := htu
  rcases (triHexPlanarFiniteStar_pfdFace_eq_inner_iff
    hNm u (hexagonalBrickFaceLeft t.1)).mp hrep with hleft | hright
  · apply Subtype.ext
    have h1 : t.1 1 = u.1 1 := by
      have := congrFun hleft 1
      simp [hexagonalBrickFaceLeft] at this
      omega
    have h0 : t.1 0 = u.1 0 := by
      have := congrFun hleft 0
      simp [hexagonalBrickFaceLeft] at this
      omega
    exact face_site_eq_of_coords h0 h1
  · have h1 : t.1 1 = u.1 1 := by
      have := congrFun hright 1
      simp [hexagonalBrickFaceLeft, hexagonalBrickFaceRight] at this
      omega
    have hbad := congrFun hright 0
    simp [hexagonalBrickFaceLeft, hexagonalBrickFaceRight, h1] at hbad
    omega

theorem triHexPlanarFiniteStarFace_eq_inner_iff
    {N m : Nat} (hNm : N < m)
    (t : {z : Site 2 // z ∈ box 2 N}) (u : Site 2) :
    triHexPlanarFiniteStarFace m u =
        triHexPlanarFiniteStarFace m t.1 ↔ u = t.1 := by
  constructor
  · intro hface
    rcases (triHexPlanarFiniteStar_pfdFace_eq_inner_iff hNm t
      (hexagonalBrickFaceLeft u)).mp hface with hleft | hright
    · have h1 : u 1 = t.1 1 := by
        have := congrFun hleft 1
        simp [hexagonalBrickFaceLeft] at this
        omega
      have h0 : u 0 = t.1 0 := by
        have := congrFun hleft 0
        simp [hexagonalBrickFaceLeft] at this
        omega
      exact face_site_eq_of_coords h0 h1
    · have h1 : u 1 = t.1 1 := by
        have := congrFun hright 1
        simp [hexagonalBrickFaceLeft, hexagonalBrickFaceRight] at this
        omega
      have hbad := congrFun hright 0
      simp [hexagonalBrickFaceLeft, hexagonalBrickFaceRight, h1] at hbad
      omega
  · rintro rfl
    rfl


end
end StatMech.FK.PeriodicPlanar
