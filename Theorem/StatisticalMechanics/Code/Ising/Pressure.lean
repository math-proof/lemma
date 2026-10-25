/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Pressure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Def.StatisticalMechanics.Code.Ising.Pressure
open scoped BigOperators
open Finset Filter Topology


namespace StatMech

namespace Ising

lemma Z_pos {Ω : Type*} [Fintype Ω] [Nonempty Ω] (β : ℝ) (E : Ω → ℝ) : 0 < Z β E :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty


theorem Z_prod {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂] (β : ℝ)
    (E₁ : Ω₁ → ℝ) (E₂ : Ω₂ → ℝ) :
    Z β (fun p : Ω₁ × Ω₂ => E₁ p.1 + E₂ p.2) = Z β E₁ * Z β E₂ := by
  unfold Z
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← Real.exp_add]
  ring_nf


end Ising
end StatMech
