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
import Def.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part7
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


lemma transferSpin_fvPathState (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) (k : ℕ) :
    transferSpin (fvPathState eta n tau k) =
      spin (glue eta tau) (site1 (-(n : ℤ) - 1 + k)) := by
  exact transferSpin_of_config _ _

lemma sum_bondFinsetTouch_eq_path (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) :
    (∑ e ∈ bondFinsetTouch 1 n, bond (glue eta tau) e) =
      ∑ k ∈ Finset.range (2 * n + 2),
        transferSpin (fvPathState eta n tau k) *
          transferSpin (fvPathState eta n tau (k + 1)) := by
  rw [sum_bondFinsetTouch_eq_chain]
  have henum := sum_range_eq_sum_Icc (-(n : ℤ) - 1) (2 * n + 1)
    (fun z => spin (glue eta tau) (site1 z) * spin (glue eta tau) (site1 (z + 1)))
  have htop : -(n : ℤ) - 1 + (2 * n + 1 : ℕ) = (n : ℤ) := by
    push_cast
    ring
  rw [htop] at henum
  rw [← henum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [transferSpin_fvPathState, transferSpin_fvPathState]
  congr 2
  · congr 1
    omega

lemma sum_boxFinset_eq_path (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) :
    (∑ x ∈ boxFinset 1 n, spin (glue eta tau) x) =
      ∑ k ∈ Finset.range (2 * n + 1),
        transferSpin (fvPathState eta n tau (k + 1)) := by
  rw [sum_boxFinset_eq_chain]
  have henum := sum_range_eq_sum_Icc (-(n : ℤ)) (2 * n)
    (fun z => spin (glue eta tau) (site1 z))
  have htop : -(n : ℤ) + (2 * n : ℕ) = (n : ℤ) := by
    push_cast
    ring
  rw [htop] at henum
  rw [← henum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [transferSpin_fvPathState]
  congr 2
  omega


end StatMech.FrontierB
