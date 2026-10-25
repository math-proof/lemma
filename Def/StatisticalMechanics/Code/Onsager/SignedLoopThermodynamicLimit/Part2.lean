/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopThermodynamicLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part4
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part6
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopThermodynamicLimit.Part2
open Finset SimpleGraph MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Sharpness StatMech.FrontierA
  StatMech.FrontierB

noncomputable section

noncomputable def ons_rectDualPathCriticalRatio {n : Nat}
    (embedding : KWStraightLineEmbedding
      (ons_rectDualGraph (2 * n) (2 * n)))
    (path : ons_RectDualPath (2 * n) (2 * n)) : Complex :=
  ((ons_signedLoopCriticalWeight : Complex) ^
      (2 * (ons_rectDualPathDefect path).card) *
    ons_rectDualPathDefectKWDet embedding path
      ons_signedLoopCriticalWeight) /
    ons_rectDualKWDet embedding ons_signedLoopCriticalWeight


end
end StatMech.Onsager
