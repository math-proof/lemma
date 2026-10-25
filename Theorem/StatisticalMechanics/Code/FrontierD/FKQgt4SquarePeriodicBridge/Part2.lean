/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoherentLimit.Part12
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicBridge
open Finset SimpleGraph MeasureTheory


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.FK StatMech.FK.PeriodicPlanar

noncomputable section

@[simp] theorem fkSquarePeriodicVertexEquiv_apply (n : Nat)
    (x : square.OrbitVertex n) :
    (fkSquarePeriodicVertexEquiv n x : Site 2) = (x : Site 2) := rfl


theorem fkSquarePeriodicVertexEquiv_adj (n : Nat)
    (x y : square.OrbitVertex n) :
    (square.orbitGraph n).Adj x y ↔
      (FK.boxGraph 2 n).Adj
        (fkSquarePeriodicVertexEquiv n x)
        (fkSquarePeriodicVertexEquiv n y) := by
  rfl


theorem fkSquarePeriodicVertexEquiv_boundary (n : Nat)
    (x : square.OrbitVertex n) :
    square.orbitBoundary n x ↔
      FK.boxBoundary 2 n (fkSquarePeriodicVertexEquiv n x) := by
  unfold PeriodicGraph.orbitBoundary FK.boxBoundary
  rw [mem_vertexBoundary]
  have hxbox : (x : Site 2) ∈ box 2 n := by
    exact (fkSquarePeriodic_mem_orbitBox_iff n x.1).mp x.2
  simp only [fkSquarePeriodicVertexEquiv_apply, hxbox, true_and]
  exact not_congr (fkSquarePeriodic_mem_orbitBox_iff (n - 1) x.1)


theorem fkSquarePeriodic_fkProb_reCfgIso (n : Nat) (p q : Real)
    (omega : ConfigSpace (Sym2 (FK.boxVerts 2 n))) :
    FK.fkProb (square.orbitGraph n) p q
        (FK.reCfgIso (fkSquarePeriodicVertexEquiv n) omega) =
      FK.fkProb (FK.boxGraph 2 n) p q omega := by
  exact FK.fvs_fkProb_reCfgIso
    (square.orbitGraph n) (FK.boxGraph 2 n)
    (fkSquarePeriodicVertexEquiv n)
    (fkSquarePeriodicVertexEquiv_adj n) p q omega


theorem fkSquarePeriodic_wiredFkProb_reCfgIso (n : Nat) (p q : Real)
    (omega : ConfigSpace (Sym2 (FK.boxVerts 2 n))) :
    FK.wiredFkProb (square.orbitGraph n) (square.orbitBoundary n) p q
        (FK.reCfgIso (fkSquarePeriodicVertexEquiv n) omega) =
      FK.wiredFkProb (FK.boxGraph 2 n) (FK.boxBoundary 2 n) p q omega := by
  exact FK.fvs_wiredFkProb_reCfgIso
    (square.orbitGraph n) (FK.boxGraph 2 n)
    (square.orbitBoundary n) (FK.boxBoundary 2 n)
    (fkSquarePeriodicVertexEquiv n)
    (fkSquarePeriodicVertexEquiv_adj n)
    (fkSquarePeriodicVertexEquiv_boundary n) p q omega


theorem fkSquarePeriodic_freeFinitePMF_reCfgIso (n : Nat)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (omega : ConfigSpace (Sym2 (FK.boxVerts 2 n))) :
    square.freeFinitePMF n hp hp1 hq
        (FK.reCfgIso (fkSquarePeriodicVertexEquiv n) omega) =
      FK.fkPMF (FK.boxGraph 2 n) hp hp1 hq omega := by
  rw [PeriodicGraph.freeFinitePMF, FK.fkPMF_apply, FK.fkPMF_apply,
    fkSquarePeriodic_fkProb_reCfgIso]


theorem fkSquarePeriodic_wiredFinitePMF_reCfgIso (n : Nat)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (omega : ConfigSpace (Sym2 (FK.boxVerts 2 n))) :
    square.wiredFinitePMF n hp hp1 hq
        (FK.reCfgIso (fkSquarePeriodicVertexEquiv n) omega) =
      FK.wiredFkPMF (FK.boxGraph 2 n) (FK.boxBoundary 2 n)
        hp hp1 hq omega := by
  rw [PeriodicGraph.wiredFinitePMF, FK.wiredFkPMF, PMF.ofFintype_apply,
    FK.wiredFkPMF, PMF.ofFintype_apply,
    fkSquarePeriodic_wiredFkProb_reCfgIso]


end
end StatMech.FrontierD
