/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingSHolo.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicDobrushin.Part6
open Finset Complex
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

variable (P : PlanarZ2Subgraph) (M : Type*) [Fintype M] [DecidableEq M]


namespace FKIsingDobrushinDomain

variable {P M} (D : FKIsingDobrushinDomain P M)


theorem norm_normalizedFermionicObservable_le
    (delta : Real) (hdelta : 0 < delta) (e : M) :
    ‖D.normalizedFermionicObservable delta e‖ <=
      1 / Real.sqrt (2 * delta) := by
  have hsqrt : 0 < Real.sqrt (2 * delta) := Real.sqrt_pos.2 (by positivity)
  unfold normalizedFermionicObservable
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt]
  exact div_le_div_of_nonneg_right (D.norm_fermionicObservable_le_one e)
    hsqrt.le


theorem normalizedFermionicObservable_terminal (delta : Real) :
    D.normalizedFermionicObservable delta D.terminalEdge =
      1 / (Real.sqrt (2 * delta) : Complex) := by
  rw [normalizedFermionicObservable, D.fermionicObservable_terminal]


end FKIsingDobrushinDomain
end
end StatMech.Universality
