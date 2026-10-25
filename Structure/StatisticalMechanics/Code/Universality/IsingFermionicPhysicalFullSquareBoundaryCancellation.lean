/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryGeometry
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryCancellation.Part3


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

structure FKIsingSquarePerimeterCancellationSwitchingAt
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) where
  uncut : ¬ fkIsingSquarePerimeterMarkedCut n side k
  pairing : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V) ≃
    ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)
  paired_summand : ∀ omega,
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand
        (pairing omega)
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquarePerimeterCancelledSide side)) =
      -(fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquarePerimeterCancelledSide side))


structure FKIsingSquarePerimeterGlobalPathSwitchingAt
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) where
  uncut : ¬ fkIsingSquarePerimeterMarkedCut n side k
  pairing : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V) ≃
    ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)
  visited : ∀ omega,
    (.dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquarePerimeterCancelledSide side) :
        FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareWiredDobrushinDomain n hn).exploration (pairing omega) ↔
      (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquarePerimeterCancelledSide side) :
          FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareWiredDobrushinDomain n hn).exploration omega
  mass : ∀ omega,
    (fkIsingSquareWiredDobrushinDomain n hn).criticalMass (pairing omega) =
      (fkIsingSquareWiredDobrushinDomain n hn).criticalMass omega
  phase : ∀ omega,
    (.dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquarePerimeterCancelledSide side) :
        FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareWiredDobrushinDomain n hn).exploration omega →
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (pairing omega)
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquarePerimeterCancelledSide side)) =
        -(fkIsingSquareWiredDobrushinDomain n hn).windingPhase omega
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquarePerimeterCancelledSide side))


structure FKIsingSquarePerimeterOppositeCarrierSwitchingAt
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) where
  uncut : ¬ fkIsingSquarePerimeterMarkedCut n side k
  mate : FKIsingSquareWiredCarrier n
  pairing : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V) ≃
    ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)
  visited : ∀ omega,
    (.dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquarePerimeterCancelledSide side) :
        FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareWiredDobrushinDomain n hn).exploration (pairing omega) ↔
      mate ∈ (fkIsingSquareWiredDobrushinDomain n hn).exploration omega
  mass : ∀ omega,
    (fkIsingSquareWiredDobrushinDomain n hn).criticalMass (pairing omega) =
      (fkIsingSquareWiredDobrushinDomain n hn).criticalMass omega
  phase : ∀ omega,
    mate ∈ (fkIsingSquareWiredDobrushinDomain n hn).exploration omega →
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (pairing omega)
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquarePerimeterCancelledSide side)) =
        -(fkIsingSquareWiredDobrushinDomain n hn).windingPhase omega mate


end
end StatMech.Universality
