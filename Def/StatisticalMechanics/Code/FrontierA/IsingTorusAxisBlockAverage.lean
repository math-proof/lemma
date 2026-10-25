/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusAxisMonotonicity
import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredBlockAverage
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusAxisBlockAverage
open Finset Set
open scoped BigOperators


namespace StatMech.FrontierA

variable {Gamma : Type*} [AddCommGroup Gamma]


section FiniteGreen

variable [Fintype Gamma]


noncomputable def finiteTorusZeroModeGreen
    (dispersion : AddChar Gamma Complex → Real) (z : Gamma) : Real :=
  (1 / Fintype.card Gamma : Real) *
    ∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex),
      (starRingEnd Complex (chi z)).re / dispersion chi

end FiniteGreen
end StatMech.FrontierA
