/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquarePrimitive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGhost.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquarePrimitive.Part2
open SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareRadialPatchFullValue_eq_primitive
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (base : Real)
    (vertexH : FKIsingSquareFullVertexNode n → Real)
    (faceH : FKIsingSquareFullFaceNode n → Real)
    (hcompatible : FKIsingSquareFullPrimitiveCompatible n hn vertexH faceH)
    (hbase : fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH
      ⟨0, by omega⟩ ⟨0, by omega⟩ = base) :
    ∀ i j : Fin m,
      fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH i j =
        base + fkIsingSquareRadialPatchPrimitive
          n m hn hm (by omega) i.1 j.1 := by
  let G := fkIsingSquareRadialPatchFullValueNat n m hm hm2 vertexH faceH
  have hGbase : G 0 0 = base := by
    have hmpos : 0 < m := by omega
    simpa [G, fkIsingSquareRadialPatchFullValueNat, hmpos] using hbase
  have hGh : ∀ i < m - 1, G (i + 1) 0 - G i 0 =
      fkIsingSquareRadialPatchHorizontalSignedIncrement
        n m hn hm (by omega) i 0 := by
    intro i hi
    have hi' : i + 1 < m := by omega
    have hi0 : i < m := by omega
    have hmpos : 0 < m := by omega
    have h := fkIsingSquareRadialPatchFullValue_horizontal_increment
      n m hn hm hm2 vertexH faceH hcompatible i 0 hi' (by omega)
    simpa [G, fkIsingSquareRadialPatchFullValueNat,
      hi', hi0, hmpos] using h
  have hGv : ∀ i ≤ m - 1, ∀ j < m - 1,
      G i (j + 1) - G i j =
        fkIsingSquareRadialPatchVerticalSignedIncrement
          n m hn hm (by omega) i j := by
    intro i hi j hj
    have hi' : i < m := by omega
    have hj' : j + 1 < m := by omega
    have hj0 : j < m := by omega
    have h := fkIsingSquareRadialPatchFullValue_vertical_increment
      n m hn hm hm2 vertexH faceH hcompatible i j hi' hj'
    simpa [G, fkIsingSquareRadialPatchFullValueNat,
      hi', hj', hj0] using h
  have hu := isingRectanglePrimitiveWithBase_eq_of_local_increments base
    (fkIsingSquareRadialPatchHorizontalSignedIncrement
      n m hn hm (by omega))
    (fkIsingSquareRadialPatchVerticalSignedIncrement
      n m hn hm (by omega)) G (m - 1) (m - 1) hGbase hGh hGv
  intro i j
  have hij := hu i.1 (by omega) j.1 (by omega)
  simpa [G, fkIsingSquareRadialPatchFullValueNat,
    fkIsingSquareRadialPatchPrimitive] using hij

theorem fkIsingSquareRadialPatchPrimalValue_eq_full_of_compatible
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (base : Real)
    (vertexH : FKIsingSquareFullVertexNode n → Real)
    (faceH : FKIsingSquareFullFaceNode n → Real)
    (hcompatible : FKIsingSquareFullPrimitiveCompatible n hn vertexH faceH)
    (hbase : fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH
      ⟨0, by omega⟩ ⟨0, by omega⟩ = base) :
    ∀ p : FKIsingSquareRadialPatchPrimalNode m,
      fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p =
        vertexH (fkIsingSquareRadialPatchPrimalFullVertex n m hm p) := by
  intro p
  have h := fkIsingSquareRadialPatchFullValue_eq_primitive
    n m hn hm hm2 base
    vertexH faceH hcompatible hbase p.1.1 p.1.2
  rw [show fkIsingSquareRadialPatchFullValue
      n m hm hm2 vertexH faceH p.1.1 p.1.2 =
      vertexH (fkIsingSquareRadialPatchPrimalFullVertex n m hm p) by
    simp [fkIsingSquareRadialPatchFullValue, p.2]] at h
  exact h.symm

theorem fkIsingSquareRadialPatchDualValue_eq_full_of_compatible
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (base : Real)
    (vertexH : FKIsingSquareFullVertexNode n → Real)
    (faceH : FKIsingSquareFullFaceNode n → Real)
    (hcompatible : FKIsingSquareFullPrimitiveCompatible n hn vertexH faceH)
    (hbase : fkIsingSquareRadialPatchFullValue n m hm hm2 vertexH faceH
      ⟨0, by omega⟩ ⟨0, by omega⟩ = base) :
    ∀ q : FKIsingSquareRadialPatchDualNode m,
      fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q =
        faceH (fkIsingSquareRadialPatchDualFullFace n m hm hm2 q) := by
  intro q
  have h := fkIsingSquareRadialPatchFullValue_eq_primitive
    n m hn hm hm2 base
    vertexH faceH hcompatible hbase q.1.1 q.1.2
  rw [show fkIsingSquareRadialPatchFullValue
      n m hm hm2 vertexH faceH q.1.1 q.1.2 =
      faceH (fkIsingSquareRadialPatchDualFullFace n m hm hm2 q) by
    simp [fkIsingSquareRadialPatchFullValue, q.2]] at h
  exact h.symm


theorem fkIsingSquareRadialPatch_unitRange_of_fullSquareGhost_compatible
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (base : Real)
    (vertexH : FKIsingSquareFullVertexNode n → Real)
    (faceH : FKIsingSquareFullFaceNode n → Real)
    (hvertexModified : ∀ x,
      ¬ fkIsingSquareFullVertexFixedBoundary n x →
        isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) vertexH x +
          isingFermionicGhostRate
            (fkIsingSquareFullVertexGhostMultiplicity n) x *
              (1 - vertexH x) ≤ 0)
    (hvertexFixed : ∀ x,
      fkIsingSquareFullVertexFixedBoundary n x → 0 ≤ vertexH x)
    (hfaceModified : ∀ c,
      ¬ fkIsingSquareFullFaceFixedBoundary n c →
        0 ≤ isingFiniteGraphLaplacian
          (fkIsingSquareFullFaceGraph n) faceH c +
            isingFermionicGhostRate
              (fkIsingSquareFullFaceGhostMultiplicity n) c *
                (0 - faceH c))
    (hfaceFixed : ∀ c,
      fkIsingSquareFullFaceFixedBoundary n c → faceH c ≤ 1)
    (hcompatible :
      FKIsingSquareFullPrimitiveCompatible n hn vertexH faceH)
    (hbase : fkIsingSquareRadialPatchFullValue
      n m hm hm2 vertexH faceH ⟨0, by omega⟩ ⟨0, by omega⟩ = base) :
    (∀ p, 0 ≤ fkIsingSquareRadialPatchPrimalValue
        n m hn hm (by omega) base p ∧
      fkIsingSquareRadialPatchPrimalValue
        n m hn hm (by omega) base p ≤ 1) ∧
      (∀ q, 0 ≤ fkIsingSquareRadialPatchDualValue
          n m hn hm (by omega) base q ∧
        fkIsingSquareRadialPatchDualValue
          n m hn hm (by omega) base q ≤ 1) := by
  apply fkIsingSquareRadialPatch_unitRange_of_fullSquareGhost
    n m hn hm hm2 base vertexH faceH hvertexModified hvertexFixed
      hfaceModified hfaceFixed
  · exact fkIsingSquareRadialPatchPrimalValue_eq_full_of_compatible
      n m hn hm hm2 base vertexH faceH hcompatible hbase
  · exact fkIsingSquareRadialPatchDualValue_eq_full_of_compatible
      n m hn hm hm2 base vertexH faceH hcompatible hbase

end
end StatMech.Universality
