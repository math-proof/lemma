/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanInclusionExclusion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanInclusionExclusion.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

namespace RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


noncomputable def aie_mass (ends : ι → Sym2 V) (m : Finset ι) (φ : Finset ι → ℝ) (S : Finset V) :
    ℝ :=
  ∑ K ∈ m.powerset.filter (fun K => sources ends K = S), φ K


noncomputable def aie_gap (ends : ι → Sym2 V) (m : Finset ι) (φ : Finset ι → ℝ) (A : Finset V)
    (o x y : V) : ℝ :=
  aie_mass ends m φ A - aie_mass ends m φ (A ∆ {x, y})
    - aie_mass ends m φ (A ∆ {o, y}) - aie_mass ends m φ (A ∆ {o, x})


end RandomCurrent
end Sharpness
end StatMech
