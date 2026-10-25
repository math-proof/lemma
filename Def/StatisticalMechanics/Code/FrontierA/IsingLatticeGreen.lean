/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingLatticeGreen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSparseGreenDecay
import Theorem.StatisticalMechanics.Code.FrontierA.IsingLatticeGreen
open Filter Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Lattice


noncomputable def isingLatticeGreen (d : Nat) (x : Site d) : Real :=
  limUnder atTop (fun k => isingDyadicTorusGreen x k)

end StatMech.FrontierA
