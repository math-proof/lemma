/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3


namespace StatMech.FrontierA

open ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def agreementFiber (K : Set E) (omega : ConfigSpace E) :
    Finset (ConfigSpace E) := by
  classical
  exact Finset.univ.filter (agreeOn K omega)

end StatMech.FrontierA
