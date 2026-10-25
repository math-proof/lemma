/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGhost.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFiniteGhostComparison.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRangeTransfer
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGhost.Part4
open SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareRadialPatchDualFullFace_key
    (n m : Nat) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (q : FKIsingSquareRadialPatchDualNode m) :
    fkIsingSquareInteriorCellKey n
        (fkIsingSquareRadialPatchDualFullFace n m hm hm2 q) =
      (((q.1.1.1 + q.1.2.1 + 1) / 2 : Int) - 1,
        (q.1.1.1 : Int) -
          ((q.1.1.1 + q.1.2.1 + 1) / 2 : Int)) := by
  have hmod := Nat.not_even_iff.mp q.2
  have hi := q.1.1.2
  have hj := q.1.2.2
  apply Prod.ext
  · simp [fkIsingSquareInteriorCellKey,
      fkIsingSquareRadialPatchDualFullFace]
    omega
  · simp [fkIsingSquareInteriorCellKey,
      fkIsingSquareRadialPatchDualFullFace]
    omega

theorem fkIsingSquareRadialPatchDualFullFace_injective
    (n m : Nat) (hm : m ≤ n) (hm2 : 2 ≤ m) :
    Function.Injective
      (fkIsingSquareRadialPatchDualFullFace n m hm hm2) := by
  intro p q hpq
  have h0 := congrArg
    (fun c : FKIsingSquareFullFaceNode n ↦ c.1.1) hpq
  have h1 := congrArg
    (fun c : FKIsingSquareFullFaceNode n ↦ c.2.1) hpq
  simp only [fkIsingSquareRadialPatchDualFullFace] at h0 h1
  have hpmod := Nat.not_even_iff.mp p.2
  have hqmod := Nat.not_even_iff.mp q.2
  have hhalf :
      (p.1.1.1 + p.1.2.1 + 1) / 2 =
        (q.1.1.1 + q.1.2.1 + 1) / 2 := by
    omega
  have hi : p.1.1.1 = q.1.1.1 := by omega
  have hj : p.1.2.1 = q.1.2.1 := by omega
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.ext hi
  · exact Fin.ext hj


theorem fkIsingSquareRadialPatch_unitRange_of_fullSquareGhost
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
    (hprimalRestriction : ∀ p,
      fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p =
        vertexH (fkIsingSquareRadialPatchPrimalFullVertex n m hm p))
    (hdualRestriction : ∀ q,
      fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q =
        faceH (fkIsingSquareRadialPatchDualFullFace n m hm hm2 q)) :
    (∀ p, 0 ≤ fkIsingSquareRadialPatchPrimalValue
        n m hn hm (by omega) base p ∧
      fkIsingSquareRadialPatchPrimalValue
        n m hn hm (by omega) base p ≤ 1) ∧
      (∀ q, 0 ≤ fkIsingSquareRadialPatchDualValue
          n m hn hm (by omega) base q ∧
        fkIsingSquareRadialPatchDualValue
          n m hn hm (by omega) base q ≤ 1) := by
  apply fkIsingSquareRadialPatch_unitRange_of_primalLower_dualUpper
    n m hn hm hm2 base
  · intro p
    rw [hprimalRestriction p]
    exact fkIsingSquareFullVertex_zero_le_of_modifiedSuperharmonic
      n vertexH hvertexModified hvertexFixed _
  · intro q
    rw [hdualRestriction q]
    exact fkIsingSquareFullFace_le_one_of_modifiedSubharmonic
      n faceH hfaceModified hfaceFixed _

end
end StatMech.Universality
