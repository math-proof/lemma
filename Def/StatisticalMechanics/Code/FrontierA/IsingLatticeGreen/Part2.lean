/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingLatticeGreen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSparseGreenDecay
import Theorem.StatisticalMechanics.Code.FrontierA.IsingLatticeGreen.Part2
open Filter Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Lattice


noncomputable def isingDyadicGreenAxisBlockAverage
    {d : Nat} (i : Fin d) (r k : Nat) : Real :=
  (1 / ((r + 1 : Nat) : Real) ^ 2) *
    ∑ a ∈ Finset.range (r + 1),
      ∑ b ∈ Finset.range (r + 1),
        isingDyadicTorusGreen
          (Pi.single i ((b : Int) - (a : Int))) k


noncomputable def isingLatticeGreenAxisBlockAverage
    {d : Nat} (i : Fin d) (r : Nat) : Real :=
  (1 / ((r + 1 : Nat) : Real) ^ 2) *
    ∑ a ∈ Finset.range (r + 1),
      ∑ b ∈ Finset.range (r + 1),
        isingLatticeGreen d (Pi.single i ((b : Int) - (a : Int)))


end StatMech.FrontierA
