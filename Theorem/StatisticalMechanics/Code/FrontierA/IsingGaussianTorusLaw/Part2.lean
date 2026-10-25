/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTorusLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusLaplacianNormalization.Part4
import Theorem.StatisticalMechanics.Code.FK.HolleyCoupling.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianTorusLaw.Part2
open Finset MeasureTheory
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising

noncomputable section

variable {d k : Nat}


theorem isingTorusZeroFieldLaw_real_singleton (beta : Real)
    (sigma : ConfigSpace (IsingDyadicTorus d k)) :
    ((isingTorusZeroFieldLaw (d := d) (k := k) beta :
        ProbabilityMeasure (ConfigSpace (IsingDyadicTorus d k))) :
      Measure (ConfigSpace (IsingDyadicTorus d k))).real {sigma} =
      isingTorusZeroFieldMass beta sigma := by
  rw [isingTorusZeroFieldLaw, ProbabilityMeasure.coe_mk,
    FK.measOfMass_real _ (isingTorusZeroFieldMass_nonneg beta)]
  simp


theorem integral_isingTorusZeroFieldLaw (beta : Real)
    (g : ConfigSpace (IsingDyadicTorus d k) -> Real) :
    ∫ sigma, g sigma
        ∂(isingTorusZeroFieldLaw (d := d) (k := k) beta :
          ProbabilityMeasure (ConfigSpace (IsingDyadicTorus d k))) =
      ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        isingTorusZeroFieldMass beta sigma * g sigma := by
  rw [integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [isingTorusZeroFieldLaw_real_singleton beta, smul_eq_mul]


end
end StatMech.FrontierA
