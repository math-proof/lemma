/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Pressure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Def.StatisticalMechanics.Code.Ising.Pressure.Part4
open scoped BigOperators
open Finset Filter Topology


namespace StatMech

namespace Ising

theorem pressure_exists {Ω : Type*} [Fintype Ω] [Nonempty Ω] (β : ℝ) (E : Ω → ℝ) :
    Tendsto (fun n => logZSeq β E n / n) atTop (𝓝 (pressure β E)) :=
  (logZSeq_subadditive β E).tendsto_lim (logZSeq_bddBelow β E)


theorem pressure_eq_logZ {Ω : Type*} [Fintype Ω] [Nonempty Ω] (β : ℝ) (E : Ω → ℝ) :
    pressure β E = Real.log (Z β E) := by
  have hlim : Tendsto (fun n => logZSeq β E n / n) atTop (𝓝 (Real.log (Z β E))) := by
    have hc : Tendsto (fun n : ℕ => (n : ℝ) * Real.log (Z β E) / n) atTop
        (𝓝 (Real.log (Z β E))) := by
      refine (tendsto_const_nhds (x := Real.log (Z β E))).congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      rw [mul_div_cancel_left₀ _ (by exact_mod_cast hn.ne')]
    refine hc.congr fun n => ?_
    rw [logZSeq_eq]
  exact tendsto_nhds_unique (pressure_exists β E) hlim


variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem isingZ_eq_Z (β h : ℝ) : isingZ G β h = Z β (hamiltonian G h) := rfl


theorem ising_pressure_exists (β h : ℝ) :
    Tendsto (fun n => logZSeq β (hamiltonian G h) n / n) atTop
      (𝓝 (pressure β (hamiltonian G h))) :=
  pressure_exists β (hamiltonian G h)


theorem ising_pressure_eq (β h : ℝ) :
    pressure β (hamiltonian G h) = Real.log (isingZ G β h) := by
  rw [pressure_eq_logZ, isingZ_eq_Z]

end Ising
end StatMech
