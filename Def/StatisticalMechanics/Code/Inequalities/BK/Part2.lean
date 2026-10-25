/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.BK
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

open ConfigSpace


variable {E F : Type*}


noncomputable def wprob [Fintype E] [DecidableEq E] (φ : E → Bool → ℝ)
    (S : Set (ConfigSpace E)) : ℝ :=
  ∑ ω, S.indicator (fun _ => (1 : ℝ)) ω * pweight φ ω


end StatMech
