/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquarePrimitive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGhost.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquarePrimitive
open SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareRadialPatchFullValue_horizontal_increment
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (vertexH : FKIsingSquareFullVertexNode n → Real)
    (faceH : FKIsingSquareFullFaceNode n → Real)
    (hcompatible : FKIsingSquareFullPrimitiveCompatible n hn vertexH faceH)
    (i j : Nat) (hi : i + 1 < m) (hj : j < m) :
    fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH
          ⟨i + 1, hi⟩ ⟨j, hj⟩ -
        fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH
          ⟨i, by omega⟩ ⟨j, hj⟩ =
      fkIsingSquareRadialPatchHorizontalSignedIncrement
        n m hn hm (by omega) i j := by
  let e := fkIsingSquareRadialPatchHorizontalIncidence
    n m hn hm (by omega) i j
  have hc := hcompatible e
  by_cases heven : Even (i + j)
  · have hnext : ¬ Even ((i + 1) + j) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    rw [fkIsingSquareRadialPatchHorizontal_face_of_even
        n m hn hm (by omega) i j hi hj heven,
      fkIsingSquareRadialPatchHorizontal_endpoint_of_even
        n m hn hm (by omega) i j hi hj heven] at hc
    simpa [fkIsingSquareRadialPatchFullValue, heven, hnext,
      fkIsingSquareRadialPatchHorizontalSignedIncrement, e] using hc
  · have hnext : Even ((i + 1) + j) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    rw [fkIsingSquareRadialPatchHorizontal_face_of_odd
        n m hn hm (by omega) i j hi hj heven,
      fkIsingSquareRadialPatchHorizontal_endpoint_of_odd
        n m hn hm (by omega) i j hi hj heven] at hc
    simp only [fkIsingSquareRadialPatchFullValue, hnext, heven,
      dite_true, dite_false,
      fkIsingSquareRadialPatchHorizontalSignedIncrement, if_false]
    change _ = -fkIsingSquareInteriorRadialIncrement n hn e
    linarith

theorem fkIsingSquareRadialPatchFullValue_vertical_increment
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (vertexH : FKIsingSquareFullVertexNode n → Real)
    (faceH : FKIsingSquareFullFaceNode n → Real)
    (hcompatible : FKIsingSquareFullPrimitiveCompatible n hn vertexH faceH)
    (i j : Nat) (hi : i < m) (hj : j + 1 < m) :
    fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH
          ⟨i, hi⟩ ⟨j + 1, hj⟩ -
        fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH
          ⟨i, hi⟩ ⟨j, by omega⟩ =
      fkIsingSquareRadialPatchVerticalSignedIncrement
        n m hn hm (by omega) i j := by
  let e := fkIsingSquareRadialPatchVerticalIncidence
    n m hn hm (by omega) i j
  have hc := hcompatible e
  by_cases heven : Even (i + j)
  · have hnext : ¬ Even (i + (j + 1)) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    rw [fkIsingSquareRadialPatchVertical_face_of_even
        n m hn hm (by omega) i j hi hj heven,
      fkIsingSquareRadialPatchVertical_endpoint_of_even
        n m hn hm (by omega) i j hi hj heven] at hc
    simpa [fkIsingSquareRadialPatchFullValue, heven, hnext,
      fkIsingSquareRadialPatchVerticalSignedIncrement, e] using hc
  · have hnext : Even (i + (j + 1)) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    rw [fkIsingSquareRadialPatchVertical_face_of_odd
        n m hn hm (by omega) i j hi hj heven,
      fkIsingSquareRadialPatchVertical_endpoint_of_odd
        n m hn hm (by omega) i j hi hj heven] at hc
    simp only [fkIsingSquareRadialPatchFullValue, hnext, heven,
      dite_true, dite_false,
      fkIsingSquareRadialPatchVerticalSignedIncrement, if_false]
    change _ = -fkIsingSquareInteriorRadialIncrement n hn e
    linarith

end
end StatMech.Universality
