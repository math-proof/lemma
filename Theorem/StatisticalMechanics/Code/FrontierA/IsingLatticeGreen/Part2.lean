/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingLatticeGreen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSparseGreenDecay
import Def.StatisticalMechanics.Code.FrontierA.IsingLatticeGreen
open Filter Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Lattice


theorem isingDyadicTorusGreen_tendsto_latticeGreen
    {d : Nat} (hd : 2 < d) (x : Site d) :
    Tendsto (fun k => isingDyadicTorusGreen x k) atTop
      (nhds (isingLatticeGreen d x)) := by
  exact (isingDyadicTorusGreen_cauchySeq hd x).tendsto_limUnder


end StatMech.FrontierA
