/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalWilson.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonAffine.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalWilson.Part2
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

noncomputable section

def cubicalXYSheet {a b c : Nat} (k : Fin (c + 1)) :
    Finset (CubicalPlaquette a b c) :=
  (Finset.univ : Finset (Fin a × Fin b)).image
    fun ij => CubicalPlaquette.xy ij.1 ij.2 k


def cubicalXYLoop {a b c : Nat} (k : Fin (c + 1)) :
    Finset (CubicalEdge a b c) :=
  gaugeSurfaceBoundary cubicalPlaquetteIncidence (cubicalXYSheet k)


end
end StatMech.FrontierA
