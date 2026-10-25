/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialIncidenceFiber
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGhost.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIncidence.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareFullIncidenceOfAdjacent_endpoint
    (n : Nat) (hn : 0 < n)
    (x : FKIsingSquareFullVertexNode n)
    (c : FKIsingSquareFullFaceNode n)
    (h : FKIsingSquareFullRadiallyAdjacent n x c) :
    fkIsingSquareInteriorRadialEndpoint n hn
        (fkIsingSquareFullIncidenceOfAdjacent n hn x c h) = x :=
  (Classical.choose_spec
    (fkIsingSquareFull_exists_incidence_of_radiallyAdjacent n hn x c h)).1

@[simp] theorem fkIsingSquareFullIncidenceOfAdjacent_faceKey
    (n : Nat) (hn : 0 < n)
    (x : FKIsingSquareFullVertexNode n)
    (c : FKIsingSquareFullFaceNode n)
    (h : FKIsingSquareFullRadiallyAdjacent n x c) :
    fkIsingSquareInteriorRadialFaceKey n hn
        (fkIsingSquareFullIncidenceOfAdjacent n hn x c h) =
      fkIsingSquareInteriorCellKey n c :=
  (Classical.choose_spec
    (fkIsingSquareFull_exists_incidence_of_radiallyAdjacent n hn x c h)).2

@[simp] theorem fkIsingSquareFullIncidenceOfAdjacent_fullFace
    (n : Nat) (hn : 0 < n)
    (x : FKIsingSquareFullVertexNode n)
    (c : FKIsingSquareFullFaceNode n)
    (h : FKIsingSquareFullRadiallyAdjacent n x c) :
    fkIsingSquareFullFaceOfRadialIncidence n hn
        (fkIsingSquareFullIncidenceOfAdjacent n hn x c h) = c := by
  apply fkIsingSquareInteriorCellKey_injective n
  rw [fkIsingSquareFullFaceOfRadialIncidence_key,
    fkIsingSquareFullIncidenceOfAdjacent_faceKey]

theorem fkIsingSquareFullIncidenceOfAdjacent_unique
    (n : Nat) (hn : 0 < n)
    (x : FKIsingSquareFullVertexNode n)
    (c : FKIsingSquareFullFaceNode n)
    (h : FKIsingSquareFullRadiallyAdjacent n x c)
    (e : FKIsingSquareInteriorRadialIncidence n hn)
    (hend : fkIsingSquareInteriorRadialEndpoint n hn e = x)
    (hface : fkIsingSquareFullFaceOfRadialIncidence n hn e = c) :
    e = fkIsingSquareFullIncidenceOfAdjacent n hn x c h := by
  apply fkIsingSquareInteriorRadialIncidence_ext n hn
  · simpa using hend
  · rw [fkIsingSquareFullIncidenceOfAdjacent_faceKey]
    rw [← fkIsingSquareFullFaceOfRadialIncidence_key n hn e, hface]

theorem fkIsingSquareFullVertexCoordinate_injective (n : Nat) :
    Function.Injective (fkIsingSquareFullVertexCoordinate n) := by
  intro x y h
  have h0 := congrArg Prod.fst h
  have h1 := congrArg Prod.snd h
  simp [fkIsingSquareFullVertexCoordinate] at h0 h1
  apply Subtype.ext
  funext k
  fin_cases k
  · change x.1 0 = y.1 0
    omega
  · change x.1 1 = y.1 1
    omega

theorem fkIsingSquareFullFaceCoordinate_injective (n : Nat) :
    Function.Injective (fkIsingSquareFullFaceCoordinate n) := by
  intro c d h
  apply fkIsingSquareInteriorCellKey_injective n
  have h0 := congrArg Prod.fst h
  have h1 := congrArg Prod.snd h
  simp [fkIsingSquareFullFaceCoordinate] at h0 h1
  apply Prod.ext <;> omega

theorem fkIsingSquareFullRadialNodeCoordinate_injective (n : Nat) :
    Function.Injective (fkIsingSquareFullRadialNodeCoordinate n) := by
  intro a b h
  cases a with
  | inl x =>
      cases b with
      | inl y =>
          exact congrArg Sum.inl
            (fkIsingSquareFullVertexCoordinate_injective n h)
      | inr c =>
          exfalso
          have heven := fkIsingSquareFullVertexCoordinate_sum_even n x
          have hodd := fkIsingSquareFullFaceCoordinate_sum_not_even n c
          change fkIsingSquareFullVertexCoordinate n x =
            fkIsingSquareFullFaceCoordinate n c at h
          rw [h] at heven
          exact hodd heven
  | inr c =>
      cases b with
      | inl x =>
          exfalso
          have heven := fkIsingSquareFullVertexCoordinate_sum_even n x
          have hodd := fkIsingSquareFullFaceCoordinate_sum_not_even n c
          change fkIsingSquareFullFaceCoordinate n c =
            fkIsingSquareFullVertexCoordinate n x at h
          rw [← h] at heven
          exact hodd heven
      | inr d =>
          exact congrArg Sum.inr
            (fkIsingSquareFullFaceCoordinate_injective n h)

theorem fkIsingSquareFull_radiallyAdjacent_of_incidence
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    FKIsingSquareFullRadiallyAdjacent n
      (fkIsingSquareInteriorRadialEndpoint n hn e)
      (fkIsingSquareFullFaceOfRadialIncidence n hn e) := by
  simpa [FKIsingSquareFullRadiallyAdjacent,
    fkIsingSquareFullVertexCoordinate,
    fkIsingSquareFullFaceCoordinate,
    fkIsingSquareInteriorRadialPrimalCoordinate,
    fkIsingSquareInteriorRadialFaceCoordinate] using
      fkIsingSquareInteriorRadial_coordinates_adjacent n hn e

theorem fkIsingSquareFullIncidenceOfAdjacent_of_incidence
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    fkIsingSquareFullIncidenceOfAdjacent n hn
        (fkIsingSquareInteriorRadialEndpoint n hn e)
        (fkIsingSquareFullFaceOfRadialIncidence n hn e)
        (fkIsingSquareFull_radiallyAdjacent_of_incidence n hn e) = e := by
  symm
  apply fkIsingSquareFullIncidenceOfAdjacent_unique
  · rfl
  · rfl

end
end StatMech.Universality
