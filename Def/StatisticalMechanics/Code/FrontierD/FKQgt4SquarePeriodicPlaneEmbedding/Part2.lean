/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicDualCoordinates
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicPlaneEmbedding
open Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.FK.PeriodicPlanar

noncomputable section

def squareComplexPeriod : Site 2 →+ Complex where
  toFun := squareComplexPoint
  map_zero' := by apply Complex.ext <;> simp
  map_add' x y := by apply Complex.ext <;> simp


def squareComplexCoordinates : Complex ≃L[Real] (Fin 2 → Real) :=
  Complex.equivRealProdCLM.trans
    (ContinuousLinearEquiv.finTwoArrow Real Real).symm

end
end StatMech.FrontierD
