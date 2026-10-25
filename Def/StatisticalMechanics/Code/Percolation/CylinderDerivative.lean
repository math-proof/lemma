/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CylinderDerivative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.CylinderDeriv.Part2
open MeasureTheory ProbabilityTheory Function Filter
open scoped ENNReal NNReal


namespace StatMech

namespace Percolation

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def measureProb (A : Set (ConfigSpace E)) (p : ℝ) : ℝ :=
  if h : 0 ≤ p ∧ p ≤ 1 then
    (bernoulliProductMeasure (E := E) ⟨p, h.1⟩ (by exact_mod_cast h.2)).real A
  else prob p A


end Percolation
end StatMech
