/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Ising.DLR
open MeasureTheory ProbabilityTheory MeasurableSpace Set
open scoped BigOperators ENNReal

set_option linter.style.longLine false


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


noncomputable def finInterSystem {Ω : Type*} (S : Set (Set Ω)) : Set (Set Ω) :=
  Set.range (fun F : Finset S => ⋂₀ (Subtype.val '' (F : Set S)))

end Ising
end StatMech
