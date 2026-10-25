/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.OneDimTransferPerron
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Def.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part6
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


@[simp] lemma transferSpin_boolTransferState (b : Bool) :
    transferSpin (boolTransferState b) = if b then 1 else -1 := by
  cases b <;> simp [boolTransferState, transferSpin]

lemma transferSpin_of_config (sigma : ConfigSpace (Site 1)) (z : ℤ) :
    transferSpin (boolTransferState (sigma (site1 z))) = spin sigma (site1 z) := by
  simp [spin]

lemma isingTransferReal_apply (beta H : ℝ) (u v : Fin 2) :
    isingTransferReal beta H u v =
      Real.exp (beta * transferSpin u * transferSpin v +
        (H / 2) * (transferSpin u + transferSpin v)) := by
  fin_cases u <;> fin_cases v <;>
    simp [isingTransferReal, transferSpin] <;> ring


end StatMech.FrontierB
