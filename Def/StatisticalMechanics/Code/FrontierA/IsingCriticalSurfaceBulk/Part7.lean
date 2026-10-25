/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalBoundaryInfluence.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectionGauge
import Abbrev.StatisticalMechanics.Code.FrontierA.IsingCriticalSurfaceBulk
open Filter MeasureTheory Topology


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Lattice StatMech.ConfigSpace
  StatMech.Sharpness

noncomputable section

noncomputable def oddPrismUnequalBridgeMoment
    (beta : Real) (n : Nat) (r : Real) : Real := by
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  exact unequalReplicaBridgeMoment
    (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
    (oddPrismUnequalGlueGraph n) beta
    (fun v => beta * oddPrismPlusField n v.1)
    (fun v => beta * oddPrismPlusField n v.1) r


noncomputable def oddPrismUnequalBridgeFreeEnergy
    (beta : Real) (n : Nat) : Real :=
  Real.log (oddPrismUnequalBridgeMoment beta n beta) -
    Real.log (oddPrismUnequalBridgeMoment beta n (-beta))

end
end StatMech.FrontierA
