/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempPlus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempCorrelation.Part2
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempPlus.Part2
open scoped BigOperators
open Finset SimpleGraph MeasureTheory


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Walls


noncomputable def ons_plusLowTempPathNumerator
    (d n : Nat) (beta : Real) {u v : Site d}
    (path : (hypercubicLattice d).Walk u v) : Real :=
  ∑ tau : {x // x ∈ box d n} → Bool,
    ons_plusLowTempPathSign (glue (plusField d) tau) path *
      Real.exp (-2 * beta) ^
        (ons_fvCutEdges (bondFinsetTouch d n)
          (glue (plusField d) tau)).card


noncomputable def ons_plusLowTempContourDenominator
    (d n : Nat) (beta : Real) : Real :=
  ∑ tau : {x // x ∈ box d n} → Bool,
    Real.exp (-2 * beta) ^
      (ons_fvCutEdges (bondFinsetTouch d n)
        (glue (plusField d) tau)).card


end StatMech.Onsager
