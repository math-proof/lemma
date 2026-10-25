/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalBoundaryInfluence.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectionGauge
import Instance.StatisticalMechanics.Code.FrontierA.IsingCriticalSurfaceBulk
open Filter MeasureTheory Topology


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Lattice StatMech.ConfigSpace
  StatMech.Sharpness

noncomputable section

abbrev OddPrismLowerBlockSite (n : Nat) :=
  {v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n //
    oddPrismAtOrBelowCenter n v}

abbrev OddPrismUpperBlockSite (n : Nat) :=
  {v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n //
    ¬ oddPrismAtOrBelowCenter n v}


noncomputable abbrev oddPrismLowerBlockGraph (n : Nat) :
    SimpleGraph (OddPrismLowerBlockSite n) :=
  StatMech.FK.agl_left (oddPrismInternalGraph n)
    (oddPrismAtOrBelowCenter n)


noncomputable abbrev oddPrismUpperBlockGraph (n : Nat) :
    SimpleGraph (OddPrismUpperBlockSite n) :=
  StatMech.FK.agl_right (oddPrismInternalGraph n)
    (oddPrismAtOrBelowCenter n)


noncomputable abbrev oddPrismUnequalGlueGraph (n : Nat) :
    SimpleGraph (OddPrismLowerBlockSite n ⊕ OddPrismUpperBlockSite n) :=
  StatMech.FK.agl_glueGraph (oddPrismInternalGraph n)
    (oddPrismAtOrBelowCenter n)


end
end StatMech.FrontierA
