/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopThermodynamicGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopThermodynamicLimit.Part3
open Finset SimpleGraph MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA StatMech.FrontierB

noncomputable section

def ons_rectDualPathRatio {n : Nat}
    (embedding : KWStraightLineEmbedding
      (ons_rectDualGraph (2 * n) (2 * n)))
    (path : ons_RectDualPath (2 * n) (2 * n))
    (beta : Real) : Complex :=
  ((Real.tanh beta : Complex) ^
      (2 * (ons_rectDualPathDefect path).card) *
    ons_rectDualPathDefectKWDet embedding path (Real.tanh beta)) /
      ons_rectDualKWDet embedding (Real.tanh beta)


end
end StatMech.Onsager
