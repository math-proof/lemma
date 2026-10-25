/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part3


namespace StatMech.FrontierA

open Matrix Finset

open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]


@[simp] theorem finiteCRSFWitnessNext_fixed
    (X : finiteCRSFWitness V) (v : V) (hv : X.1 v = v) :
    finiteCRSFWitnessNext X v = X.2 ⟨v, hv⟩ := by
  simp [finiteCRSFWitnessNext, hv]

theorem finiteCRSFWitnessNext_nonfixed_cycle
    (X : finiteCRSFWitness V) (v : V) (hv : X.1 v ≠ v) :
    finiteCRSFWitnessNext X (X.1 v) = v := by
  have hnonfixed : X.1 (X.1 v) ≠ X.1 v := by
    intro h
    exact hv (X.1.injective h)
  simp [finiteCRSFWitnessNext, hnonfixed]


theorem finiteCRSFWitnessNext_injectiveOn_support
    (X : finiteCRSFWitness V) :
    Set.InjOn (finiteCRSFWitnessNext X) X.1.support := by
  intro a ha b hb hab
  have ha' : X.1 a ≠ a := Equiv.Perm.mem_support.mp ha
  have hb' : X.1 b ≠ b := Equiv.Perm.mem_support.mp hb
  have hab' : X.1.symm a = X.1.symm b := by
    simpa only [finiteCRSFWitnessNext, dif_neg ha', dif_neg hb'] using hab
  exact X.1.symm.injective hab'


end StatMech.FrontierA
