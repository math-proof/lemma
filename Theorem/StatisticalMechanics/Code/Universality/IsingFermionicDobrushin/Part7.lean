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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicDobrushin.Part8
open Finset Complex
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

variable (P : PlanarZ2Subgraph) (M : Type*) [Fintype M] [DecidableEq M]


namespace FKIsingDobrushinDomain

variable {P M} (D : FKIsingDobrushinDomain P M)


namespace LocalSwitchingTable

variable (T : D.LocalSwitchingTable)


theorem sum_toggle (k : Fin 4) :
    (∑ omega : ConfigSpace (Sym2 P.V),
      D.fermionicSummand (T.toggle omega) (T.edges k)) =
      ∑ omega : ConfigSpace (Sym2 P.V),
        D.fermionicSummand omega (T.edges k) := by
  exact Equiv.sum_comp T.toggle
    (fun omega => D.fermionicSummand omega (T.edges k))


theorem fermionicObservable_eq_medialVertex_edgeObs (k : Fin 4) :
    D.fermionicObservable (T.edges k) = (medialVertex D T).edgeObs k := by
  have hsum :
      (∑ omega : ConfigSpace (Sym2 P.V),
        (D.fermionicSummand omega (T.edges k) +
          D.fermionicSummand (T.toggle omega) (T.edges k))) =
      ∑ omega : ConfigSpace (Sym2 P.V),
        isingF k (switchingAmplitude D T omega) := by
    apply Finset.sum_congr rfl
    intro omega _
    exact pairedContribution_switchingAmplitude D T omega k
  rw [Finset.sum_add_distrib, T.sum_toggle D k] at hsum
  have hlinear :
      (∑ omega : ConfigSpace (Sym2 P.V),
        isingF k (switchingAmplitude D T omega)) =
      isingF k (∑ omega : ConfigSpace (Sym2 P.V),
        switchingAmplitude D T omega) := by
    fin_cases k <;>
      simp [isingF, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
  rw [hlinear] at hsum
  have hhalf (X : Complex) : isingF k (X / 2) = isingF k X / 2 := by
    fin_cases k <;> simp only [isingF] <;> ring
  unfold fermionicObservable medialVertex IsingMedialVertex.edgeObs
  rw [hhalf]
  linear_combination (1 / 2 : Complex) * hsum


end LocalSwitchingTable
end FKIsingDobrushinDomain
end
end StatMech.Universality
