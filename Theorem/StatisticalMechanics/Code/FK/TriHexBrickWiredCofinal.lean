/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickDualInfiniteDomination
import Theorem.StatisticalMechanics.Code.FK.TriangularSharpnessCritical.Part10
import Def.StatisticalMechanics.Code.FK.TriHexBrickWiredCofinal
open Filter Finset MeasureTheory Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls BeffaraDC

open StatMech.OSSS

noncomputable section

theorem monotone_triangularBoxActiveRestrictLE {n m : Nat} (hnm : n ≤ m) :
    Monotone (triangularBoxActiveRestrictLE hnm) := by
  intro rho eta hrho e
  exact hrho (triangularBoxEdgeLE hnm e)


theorem triHexFaceDualInnerActive_restrictLE {n m : Nat} (hnm : n ≤ m)
    (omega : ConfigSpace (Sym2 HexVertex)) :
    triangularBoxActiveRestrictLE hnm
        (triHexFaceDualInnerActive m omega) =
      triHexFaceDualInnerActive n omega := by
  funext e
  unfold triangularBoxActiveRestrictLE restrictConfig
  unfold triHexFaceDualInnerActive
  apply congrArg (fun b : Bool => !b)
  apply congrArg omega
  apply congrArg triHexFullDualEdgeEquiv
  change edgeIncl 2 m (innerEdgeLE 2 hnm e.1) = edgeIncl 2 n e.1
  exact edgeIncl_innerEdgeLE 2 hnm e.1


end
end StatMech.FK.PeriodicPlanar
