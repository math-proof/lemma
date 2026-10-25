/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareWiredPhaseTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualInfiniteDomination
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFaceDualFrame.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareInverseDualPercolation
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityBoxInfluence
import Theorem.StatisticalMechanics.Code.IsingFK.PcUpperAllDimensions
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4SquareWiredPhaseTransport
open Filter Finset MeasureTheory Set SimpleGraph Topology


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

open StatMech.Percolation StatMech.Universality

open StatMech.FK.PeriodicPlanar

noncomputable section

theorem fkSquareActiveConnToBoundaryEvent_isIncreasing
    (N : Nat) (x : FK.boxVerts 2 N) :
    IsIncreasing (fkSquareActiveConnToBoundaryEvent N x) := by
  intro rho eta hrho hmem
  obtain ⟨y, hy, hreach⟩ := hmem
  refine ⟨y, hy, hreach.mono ?_⟩
  apply openSub_mono
  intro e
  by_cases he : e ∈ (FK.boxGraph 2 N).edgeSet
  · simpa [extendActive, he] using hrho ⟨e, he⟩
  · simp [extendActive, he]


theorem fkSquare_activeConnToBoundary_cylinder
    (N : Nat) (x : FK.boxVerts 2 N) :
    FK.boxRestrict 2 N ⁻¹'
        (restrictActive (FK.boxGraph 2 N) ⁻¹'
          fkSquareActiveConnToBoundaryEvent N x) =
      {omega : ConfigSpace (Sym2 (Site 2)) |
        IsingFK.ConnToBdry (FK.boxGraph 2 N) (FK.boxBoundary 2 N)
          (FK.boxRestrict 2 N omega) x} := by
  ext omega
  change IsingFK.ConnToBdry (FK.boxGraph 2 N) (FK.boxBoundary 2 N)
      (extendActive (FK.boxGraph 2 N)
        (restrictActive (FK.boxGraph 2 N) (FK.boxRestrict 2 N omega))) x ↔
    IsingFK.ConnToBdry (FK.boxGraph 2 N) (FK.boxBoundary 2 N)
      (FK.boxRestrict 2 N omega) x
  unfold IsingFK.ConnToBdry FK.Connected
  rw [fkSquare_openSub_extendActive_restrictActive]


theorem fkSquare_faceDualInnerEvent_connToBoundary
    (N : Nat) (x : FK.boxVerts 2 N) :
    fkSquareFaceDualInnerEvent N
        (fkSquareActiveConnToBoundaryEvent N x) =
      {omega : ConfigSpace (Sym2 (Site 2)) |
        IsingFK.ConnToBdry (FK.boxGraph 2 N) (FK.boxBoundary 2 N)
          (FK.boxRestrict 2 N (fci_faceDualConfig omega)) x} := by
  ext omega
  change IsingFK.ConnToBdry (FK.boxGraph 2 N) (FK.boxBoundary 2 N)
      (extendActive (FK.boxGraph 2 N)
        (fkSquareFaceDualInnerActive N omega)) x ↔ _
  have hactive : fkSquareFaceDualInnerActive N omega =
      restrictActive (FK.boxGraph 2 N)
        (FK.boxRestrict 2 N (fci_faceDualConfig omega)) := by
    rfl
  rw [hactive]
  unfold IsingFK.ConnToBdry FK.Connected
  rw [fkSquare_openSub_extendActive_restrictActive]
  rfl

end
end StatMech.FrontierD
