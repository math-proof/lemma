/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDobrushin.Part8
import Theorem.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part3
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part4
open Finset Complex
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingDobrushinDomain

variable {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]

variable (D : FKIsingDobrushinDomain P M)

namespace BalancedLocalSwitchingTable

variable (T : D.BalancedLocalSwitchingTable)

theorem sum_toggle (k : Fin 4) :
    (∑ omega : ConfigSpace (Sym2 P.V),
      D.fermionicSummand (T.toggle omega) (T.edges k)) =
      ∑ omega : ConfigSpace (Sym2 P.V),
        D.fermionicSummand omega (T.edges k) := by
  exact Equiv.sum_comp T.toggle
    (fun omega => D.fermionicSummand omega (T.edges k))

theorem fermionicObservable_contour_relation :
    D.fermionicObservable (T.edges 0) - D.fermionicObservable (T.edges 1) =
      Complex.I * (D.fermionicObservable (T.edges 2) -
        D.fermionicObservable (T.edges 3)) := by
  have hsum :
      (∑ omega : ConfigSpace (Sym2 P.V),
        ((D.fermionicSummand omega (T.edges 0) +
            D.fermionicSummand (T.toggle omega) (T.edges 0)) -
          (D.fermionicSummand omega (T.edges 1) +
            D.fermionicSummand (T.toggle omega) (T.edges 1)))) =
      ∑ omega : ConfigSpace (Sym2 P.V),
        Complex.I *
          ((D.fermionicSummand omega (T.edges 2) +
              D.fermionicSummand (T.toggle omega) (T.edges 2)) -
            (D.fermionicSummand omega (T.edges 3) +
              D.fermionicSummand (T.toggle omega) (T.edges 3))) := by
    apply Finset.sum_congr rfl
    intro omega _
    exact T.pairedBalance omega
  rw [← Finset.mul_sum] at hsum
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  rw [T.sum_toggle D 0, T.sum_toggle D 1,
    T.sum_toggle D 2, T.sum_toggle D 3] at hsum
  unfold fermionicObservable
  linear_combination (1 / 2 : Complex) * hsum

end BalancedLocalSwitchingTable
end FKIsingDobrushinDomain
end
end StatMech.Universality
