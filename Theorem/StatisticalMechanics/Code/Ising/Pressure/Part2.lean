/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Pressure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Def.StatisticalMechanics.Code.Ising.Pressure.Part2
open scoped BigOperators
open Finset Filter Topology


namespace StatMech

namespace Ising

theorem Zpow_eq {Ω : Type*} [Fintype Ω] (β : ℝ) (E : Ω → ℝ) (n : ℕ) :
    Zpow β E n = (Z β E) ^ n := by
  unfold Zpow Z
  have key : (∑ a, Real.exp (-β * E a)) ^ n
      = ∑ p : Fin n → Ω, ∏ i, Real.exp (-β * E (p i)) :=
    Fintype.sum_pow (fun a => Real.exp (-β * E a)) n
  rw [key]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum, Real.exp_sum]


lemma Zpow_pos {Ω : Type*} [Fintype Ω] [Nonempty Ω] (β : ℝ) (E : Ω → ℝ) (n : ℕ) :
    0 < Zpow β E n :=
  Z_pos β _


end Ising
end StatMech
