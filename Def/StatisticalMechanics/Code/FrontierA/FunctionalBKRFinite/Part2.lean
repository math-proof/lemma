/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRFinite


namespace StatMech.FrontierA

open ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def cylinderMin (f : ConfigSpace E → ℝ) (K : Set E)
    (omega : ConfigSpace E) : ℝ :=
  (agreementFiber K omega).inf' (agreementFiber_nonempty K omega) f


end StatMech.FrontierA
