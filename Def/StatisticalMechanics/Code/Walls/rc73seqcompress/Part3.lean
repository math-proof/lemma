/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc73seqcompress.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc60reimerinjection.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerStep.Part3
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Theorem.StatisticalMechanics.Code.Walls.rc73seqcompress.Part2
set_option linter.style.longLine false

open Finset


namespace StatMech.Walls

open StatMech

variable {α : Type*} [DecidableEq α]


def rc73_occ {n : ℕ} (𝒜 : Finset (Finset (Fin n))) (K S : Finset (Fin n)) : Bool :=
  decide (∀ S' : Finset (Fin n), S' ∩ K = S ∩ K → S' ∈ 𝒜)


def rc73_disjOcc {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Finset (Fin n))).filter (fun S =>
    ∃ K L : Finset (Fin n), Disjoint K L ∧ rc73_occ 𝒜 K S = true ∧ rc73_occ ℬ L S = true)


end StatMech.Walls
