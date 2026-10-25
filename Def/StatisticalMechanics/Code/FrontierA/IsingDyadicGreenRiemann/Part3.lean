/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenLowMomentum
import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredSpatial
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.MeasureTheory.Order.UpperLower
import Theorem.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenRiemann.Part2
open Bornology Filter Finset MeasureTheory Set
open scoped BigOperators ComplexConjugate Pointwise Topology


namespace StatMech.FrontierA

variable {d : Nat}

open Lattice

noncomputable def isingRegularizedTorusGreen
    (eta : Real) (x : Fin d → Int) (k : Nat) : Real :=
  (∑ p : IsingDyadicTorus d k,
      isingRegularizedGreenIntegrand eta x
        (isingTorusCenteredMomentumFun p)) /
    (isingDyadicSide k : Real) ^ d


noncomputable def isingDyadicTorusGreen
    (x : Fin d → Int) (k : Nat) : Real :=
  (∑ p : IsingDyadicTorus d k,
      if p = 0 then 0 else
        Real.cos (2 * Real.pi * ∑ i : Fin d,
          isingTorusCenteredMomentumFun p i * (x i : Real)) *
        (isingTorusCharacterDispersion
          (isingTorusMomentumChar p))⁻¹) /
    (isingDyadicSide k : Real) ^ d


def isingSiteToDyadicTorus (k : Nat) (x : Site d) :
    IsingDyadicTorus d k :=
  fun i => (x i : ZMod (isingDyadicSide k))

end StatMech.FrontierA
