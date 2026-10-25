/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeMarginalInfinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FKUniquenessSkeleton.Part3
import Theorem.StatisticalMechanics.Code.FK.Ergodicity
open MeasureTheory
open scoped BigOperators StatMech


namespace StatMech

namespace FK

section Finite

variable {E : Type*} [Fintype E] [DecidableEq E]

noncomputable def emi_gap (z : ConfigSpace E × ConfigSpace E) : ℝ :=
  ∑ e : E, ((if z.2 e then (1 : ℝ) else 0) - (if z.1 e then (1 : ℝ) else 0))

end Finite
end FK
end StatMech
