/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FiniteEventMultivalued.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MultivaluedMap
open MeasureTheory Set Finset
open scoped ENNReal BigOperators


namespace StatMech.FrontierA

variable {Omega I : Type*} [MeasurableSpace Omega]


noncomputable def finiteEventMultiplicity (J : Finset I) (A : I → Set Omega)
    (omega : Omega) : Nat := by
  classical
  exact (J.filter fun i => omega ∈ A i).card

end StatMech.FrontierA
