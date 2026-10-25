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
import Theorem.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part15
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


noncomputable def fvCenterStateProb (eta : ConfigSpace (Site 1)) (n : ℕ)
    (beta h : ℝ) (s : Fin 2) : ℝ :=
  ∑ tau : {x // x ∈ box 1 n} → Bool,
    if fvPathState eta n tau (n + 1) = s then
      fvProb eta n (bondFinsetTouch 1 n) beta h tau else 0

end StatMech.FrontierB
