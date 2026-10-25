/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusStationarity
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSimon.Part8
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempPlusBox.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGraph.Part2
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness

variable {d k : Nat}

def isingTorusIndexedEdge
    (p : IsingDyadicTorus d k × Fin d) :
    Sym2 (IsingDyadicTorus d k) :=
  s(p.1, p.1 + isingTorusStep p.2)

end StatMech.FrontierA
