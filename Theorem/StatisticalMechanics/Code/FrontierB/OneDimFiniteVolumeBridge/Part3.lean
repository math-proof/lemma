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
import Def.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part3
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


lemma chainBond_mem_bondFinsetTouch_iff (z : ℤ) (n : ℕ) :
    chainBond z ∈ bondFinsetTouch 1 n ↔
      -(n : ℤ) - 1 ≤ z ∧ z ≤ (n : ℤ) := by
  rw [chainBond, mem_bondFinsetTouch_mk_iff, site1_adj_iff,
    site1_mem_box_iff, site1_mem_box_iff]
  norm_num
  omega


end StatMech.FrontierB
