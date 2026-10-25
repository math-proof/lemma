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
open Filter Finset MeasureTheory Set SimpleGraph Topology


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

open StatMech.Percolation StatMech.Universality

open StatMech.FK.PeriodicPlanar

noncomputable section

theorem freeInfinite_faceDual_le_wiredFinite
    {R N : Nat} (hRN : R ≤ N) (hN : 1 ≤ N)
    {q : Real} (hq : 1 ≤ q)
    {A : Set (ConfigSpace (FK.boxGraph 2 R).edgeSet)}
    (hA : IsIncreasing A) :
    ((FK.freeInfiniteVolume 2
        (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).1
        (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).2
        (zero_lt_one.trans_le hq) :
      ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        (fkSquareFaceDualInnerEvent R A) ≤
      (FK.wiredFiniteMeasure 2 N
        (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).1
        (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).2
        (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        (FK.boxRestrict 2 R ⁻¹'
          (restrictActive (FK.boxGraph 2 R) ⁻¹' A)) := by
  let hp := (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).1
  let hp1 := (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).2
  let hq0 := zero_lt_one.trans_le hq
  obtain ⟨phi, hphi, hconv⟩ := FK.freeInfiniteVolume_isLimit 2 hp hp1 hq0
  have hport := hconv.tendsto_real_of_isClopen
    (isClopen_fkSquareFaceDualInnerEvent R A)
  apply le_of_tendsto hport
  filter_upwards
    [hphi.tendsto_atTop.eventually (eventually_gt_atTop N)] with n hn
  exact freeFinite_faceDual_le_wiredFinite hRN hn hN hq hA


theorem fkSquare_openSub_extendActive_restrictActive
    (N : Nat) (eta : ConfigSpace (Sym2 (FK.boxVerts 2 N))) :
    openSub (FK.boxGraph 2 N)
        (extendActive (FK.boxGraph 2 N)
          (restrictActive (FK.boxGraph 2 N) eta)) =
      openSub (FK.boxGraph 2 N) eta := by
  ext u v
  by_cases huv : (FK.boxGraph 2 N).Adj u v
  · have he : s(u, v) ∈ (FK.boxGraph 2 N).edgeSet := by
      rwa [SimpleGraph.mem_edgeSet]
    simp [openSub_adj, huv, extendActive, restrictActive, he]
  · simp [openSub_adj, huv]


end
end StatMech.FrontierD
