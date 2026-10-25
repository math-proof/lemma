/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegratedPrimitive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegration.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquarePrimitive.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalGhostEnergy
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegratedPrimitive.Part5


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareFullIntegratedPrimitive

theorem radialPatchPrimalValue_eq
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (p : FKIsingSquareRadialPatchPrimalNode m) :
    fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega)
        (radialPatchBase n m hn hm hm2) p =
      vertexPrimitive n hn
        (fkIsingSquareRadialPatchPrimalFullVertex n m hm p) := by
  exact fkIsingSquareRadialPatchPrimalValue_eq_full_of_compatible
    n m hn hm hm2 (radialPatchBase n m hn hm hm2)
      (vertexPrimitive n hn) (facePrimitive n hn) (compatible n hn) rfl p

theorem radialPatchDualValue_eq
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (q : FKIsingSquareRadialPatchDualNode m) :
    fkIsingSquareRadialPatchDualValue n m hn hm (by omega)
        (radialPatchBase n m hn hm hm2) q =
      facePrimitive n hn
        (fkIsingSquareRadialPatchDualFullFace n m hm hm2 q) := by
  exact fkIsingSquareRadialPatchDualValue_eq_full_of_compatible
    n m hn hm hm2 (radialPatchBase n m hn hm hm2)
      (vertexPrimitive n hn) (facePrimitive n hn) (compatible n hn) rfl q

theorem radialPatch_unitRange_of_fullSquareGhost
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (hvertexModified : ∀ x,
      ¬ fkIsingSquareFullVertexFixedBoundary n x →
        isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
            (vertexPrimitive n hn) x +
          isingFermionicGhostRate
            (fkIsingSquareFullVertexGhostMultiplicity n) x *
              (1 - vertexPrimitive n hn x) ≤ 0)
    (hvertexFixed : ∀ x,
      fkIsingSquareFullVertexFixedBoundary n x →
        0 ≤ vertexPrimitive n hn x)
    (hfaceModified : ∀ c,
      ¬ fkIsingSquareFullFaceFixedBoundary n c →
        0 ≤ isingFiniteGraphLaplacian
          (fkIsingSquareFullFaceGraph n) (facePrimitive n hn) c +
            isingFermionicGhostRate
              (fkIsingSquareFullFaceGhostMultiplicity n) c *
                (0 - facePrimitive n hn c))
    (hfaceFixed : ∀ c,
      fkIsingSquareFullFaceFixedBoundary n c →
        facePrimitive n hn c ≤ 1) :
    (∀ p, 0 ≤ fkIsingSquareRadialPatchPrimalValue
          n m hn hm (by omega) (radialPatchBase n m hn hm hm2) p ∧
        fkIsingSquareRadialPatchPrimalValue
          n m hn hm (by omega) (radialPatchBase n m hn hm hm2) p ≤ 1) ∧
      (∀ q, 0 ≤ fkIsingSquareRadialPatchDualValue
          n m hn hm (by omega) (radialPatchBase n m hn hm hm2) q ∧
        fkIsingSquareRadialPatchDualValue
          n m hn hm (by omega) (radialPatchBase n m hn hm hm2) q ≤ 1) := by
  exact fkIsingSquareRadialPatch_unitRange_of_fullSquareGhost_compatible
    n m hn hm hm2 (radialPatchBase n m hn hm hm2)
      (vertexPrimitive n hn) (facePrimitive n hn)
      hvertexModified hvertexFixed hfaceModified hfaceFixed
      (compatible n hn) rfl

theorem radialPatch_deepCell_energy_sq_le_of_boundary
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) (hr : 0 < r)
    (hvertexModified : ∀ x,
      ¬ fkIsingSquareFullVertexFixedBoundary n x →
        isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
            (vertexPrimitive n hn) x +
          isingFermionicGhostRate
            (fkIsingSquareFullVertexGhostMultiplicity n) x *
              (1 - vertexPrimitive n hn x) ≤ 0)
    (hvertexFixed : ∀ x,
      fkIsingSquareFullVertexFixedBoundary n x →
        0 ≤ vertexPrimitive n hn x)
    (hfaceModified : ∀ c,
      ¬ fkIsingSquareFullFaceFixedBoundary n c →
        0 ≤ isingFiniteGraphLaplacian
          (fkIsingSquareFullFaceGraph n) (facePrimitive n hn) c +
            isingFermionicGhostRate
              (fkIsingSquareFullFaceGhostMultiplicity n) c *
                (0 - facePrimitive n hn c))
    (hfaceFixed : ∀ c,
      fkIsingSquareFullFaceFixedBoundary n c →
        facePrimitive n hn c ≤ 1) :
    (((1 / (m : Real)) ^ 2) *
        ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm
                ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ /
              (Real.sqrt (2 * (1 / (m : Real))) : Complex))) ^ 2 ≤
      256 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
  exact
    fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_sq_le_of_fullSquareGhost_compatible
      n m hn hm hm2 r hr (radialPatchBase n m hn hm hm2)
      (vertexPrimitive n hn) (facePrimitive n hn)
      hvertexModified hvertexFixed hfaceModified hfaceFixed
      (compatible n hn) rfl

end FKIsingSquareFullIntegratedPrimitive
end
end StatMech.Universality
