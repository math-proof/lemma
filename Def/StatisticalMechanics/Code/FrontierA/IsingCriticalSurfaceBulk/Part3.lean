/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalBoundaryInfluence.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectionGauge
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalSurfaceBulk.Part3
open Filter MeasureTheory Topology


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Lattice StatMech.ConfigSpace
  StatMech.Sharpness

noncomputable section

noncomputable def oddPrismLowerHalfGraph (n : Nat) :
    SimpleGraph
      {v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n //
        v.z.val <= n} :=
  (oddPrismInternalGraph n).comap Subtype.val


def oddPrismLowerHalfBridgeSites (n : Nat) :
    (Fin (2 * n + 1) × Fin (2 * n + 1)) ->
      {v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n //
        v.z.val <= n} :=
  fun q => oddPrismLowerHalfSurfaceSite n q.1 q.2


noncomputable def oddPrismLowerHalfBridgeFreeEnergy
    (beta : Real) (n : Nat) : Real := by
  letI : DecidableRel (oddPrismLowerHalfGraph n).Adj := Classical.decRel _
  exact replicaBridgeFreeEnergy (oddPrismLowerHalfGraph n)
    (fun _ => beta)
    (fun v => beta * oddPrismPlusField n v.1)
    (oddPrismLowerHalfBridgeSites n) beta


end
end StatMech.FrontierA
