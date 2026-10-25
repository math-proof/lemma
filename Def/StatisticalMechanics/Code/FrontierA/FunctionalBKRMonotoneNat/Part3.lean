/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneNat.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRFinite.Part5
import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRMonotoneNat.Part2
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

open StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def cylinderMinNat (F : ConfigSpace E -> ℕ) (K : Set E)
    (omega : ConfigSpace E) : ℕ :=
  (agreementFiber K omega).inf' (agreementFiber_nonempty K omega) F


end StatMech.FrontierA
