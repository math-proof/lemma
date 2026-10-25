/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingLatticeGreen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSparseGreenDecay
import Def.StatisticalMechanics.Code.FrontierA.IsingLatticeGreen.Part2
open Filter Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Lattice


theorem isingDyadicGreenAxisBlockAverage_tendsto_latticeGreen
    {d : Nat} (hd : 2 < d) (i : Fin d) (r : Nat) :
    Tendsto (isingDyadicGreenAxisBlockAverage i r)
      atTop (nhds (isingLatticeGreenAxisBlockAverage i r)) := by
  have hsum : Tendsto
      (fun k => ∑ a ∈ Finset.range (r + 1),
        ∑ b ∈ Finset.range (r + 1),
          isingDyadicTorusGreen
            (Pi.single i ((b : Int) - (a : Int))) k)
      atTop
      (nhds (∑ a ∈ Finset.range (r + 1),
        ∑ b ∈ Finset.range (r + 1),
          isingLatticeGreen d
            (Pi.single i ((b : Int) - (a : Int))))) := by
    exact tendsto_finsetSum (Finset.range (r + 1)) fun a _ =>
      tendsto_finsetSum (Finset.range (r + 1)) fun b _ =>
        isingDyadicTorusGreen_tendsto_latticeGreen hd
          (Pi.single i ((b : Int) - (a : Int)))
  change Tendsto
    (fun k => (1 / ((r + 1 : Nat) : Real) ^ 2) *
      ∑ a ∈ Finset.range (r + 1),
        ∑ b ∈ Finset.range (r + 1),
          isingDyadicTorusGreen
            (Pi.single i ((b : Int) - (a : Int))) k)
    atTop
    (nhds ((1 / ((r + 1 : Nat) : Real) ^ 2) *
      ∑ a ∈ Finset.range (r + 1),
        ∑ b ∈ Finset.range (r + 1),
          isingLatticeGreen d
            (Pi.single i ((b : Int) - (a : Int)))))
  exact hsum.const_mul (1 / ((r + 1 : Nat) : Real) ^ 2)

end StatMech.FrontierA
