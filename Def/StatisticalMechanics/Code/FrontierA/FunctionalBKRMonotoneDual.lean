/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRMonotoneReal.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterfly
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRMonotoneDual
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

open StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]

noncomputable def dualWprob (phi : E → Bool → ℝ)
    (C : Set (ConfigSpace E × ConfigSpace E)) : ℝ :=
  ∑ omega : ConfigSpace E, ∑ eta : ConfigSpace E,
    C.indicator (fun _ => (1 : ℝ)) (omega, eta) *
      (pweight phi omega * pweight phi eta)


end StatMech.FrontierA
