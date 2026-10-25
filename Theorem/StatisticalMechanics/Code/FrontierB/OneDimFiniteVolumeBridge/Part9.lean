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
import Def.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part9
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


lemma interiorStateEquiv_apply
    (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) (k : Fin (2 * n + 1)) :
    interiorStateEquiv n tau k = fvPathState eta n tau (k.val + 1) := by
  change boolEquivFin2 (tau ((box1EquivFin n).symm k)) =
    boolTransferState
      (glue eta tau (site1 (-(n : ℤ) - 1 + ((k.val + 1 : ℕ) : ℤ))))
  have hmem : site1 (-(n : ℤ) - 1 + ((k.val + 1 : ℕ) : ℤ)) ∈ box 1 n := by
    apply (site1_mem_box_iff _ _).mpr
    have hk := k.2
    constructor <;> omega
  rw [glue_mem _ _ hmem]
  change boolTransferState (tau ((box1EquivFin n).symm k)) = _
  apply congrArg boolTransferState
  apply congrArg tau
  apply Subtype.ext
  change site1 ((k : ℤ) - n) =
    site1 (-(n : ℤ) - 1 + ((k.val + 1 : ℕ) : ℤ))
  congr 1
  push_cast
  ring


end StatMech.FrontierB
